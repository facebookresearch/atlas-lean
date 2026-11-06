/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# Regular functions between affine spaces

Ported from [`FormalConjecturesForMathlib/Algebra/MvPolynomial/RegularFunction.lean`](https://github.com/google-deepmind/formal-conjectures/blob/62f56e8e4dab933a720f649721875c478b0ecf1c/FormalConjecturesForMathlib/Algebra/MvPolynomial/RegularFunction.lean)
at pinned commit `62f56e8e4dab933a720f649721875c478b0ecf1c`.
The composition arguments follow Mathlib's usual receiver-first convention, and
the evaluation theorem is generalized to points in any commutative `k`-algebra.

A *regular function* from $k^σ$ to $k^τ$ is a $τ$-indexed family of polynomials in the
variables $σ$, i.e. a vector valued polynomial function. This file provides the basic
API: the Jacobian matrix, composition, the identity, and evaluation at a point.
-/

namespace MvPolynomial

variable {k : Type*} [CommSemiring k]
variable {σ τ ι κ : Type*}

variable (k σ τ) in
/-- **Regular functions.** For a commutative semiring $k$ and index types $\sigma$ and $\tau$, a
regular function from $k^\sigma$ to $k^\tau$ is a family $F = (F_t)_{t \in \tau}$ of polynomials
in the variables $X_s$, $s \in \sigma$, with coefficients in $k$.

The components are formal polynomials, not functions on $k^\sigma$. -/
abbrev RegularFunction := τ → MvPolynomial σ k

namespace RegularFunction

/-- **Jacobian matrix of a regular function.** The Jacobian of a regular function
$F = (F_j)_{j \in \tau}$ from $k^\sigma$ to $k^\tau$ is the $\tau \times \sigma$ matrix, with
entries in the polynomial ring $k[X_i : i \in \sigma]$, whose entry in row $j$ and column $i$ is
the formal partial derivative $\partial F_j / \partial X_i$.

Rows are indexed by the components and columns by the variables, following the usual matrix
convention, so the Jacobian multiplies column vectors indexed by $\sigma$. -/
noncomputable def Jacobian (F : RegularFunction k σ τ) :
    Matrix τ σ (MvPolynomial σ k) :=
  Matrix.of fun j i => MvPolynomial.pderiv i (F j)

@[simp]
lemma Jacobian_apply (F : RegularFunction k σ τ) (j : τ) (i : σ) :
    F.Jacobian j i = MvPolynomial.pderiv i (F j) :=
  rfl

/-- **Composition of regular functions.** For regular functions $G$ from $k^\tau$ to $k^\iota$
and $F$ from $k^\sigma$ to $k^\tau$, the composition $G \circ F$ is the regular function from
$k^\sigma$ to $k^\iota$ whose $i$-th component, for $i \in \iota$, is the polynomial obtained
from $G_i$ by substituting $F_t$ for the variable $X_t$ for every $t \in \tau$. -/
noncomputable def comp
    (G : RegularFunction k τ ι) (F : RegularFunction k σ τ) :
    RegularFunction k σ ι :=
  fun (i : ι) ↦ MvPolynomial.bind₁ F (G i)

variable (k σ) in
noncomputable def id : RegularFunction k σ σ := MvPolynomial.X

@[simp]
lemma comp_apply (G : RegularFunction k τ ι) (F : RegularFunction k σ τ) (i : ι) :
    (G.comp F) i = MvPolynomial.bind₁ F (G i) :=
  rfl

@[simp]
lemma id_apply (i : σ) : id k σ i = MvPolynomial.X i :=
  rfl

/-- **The identity is a left unit for composition.** For every regular function $F$ from
$k^\sigma$ to $k^\tau$, composing the identity regular function on $k^\tau$, whose components
are the variables $X_t$ for $t \in \tau$, with $F$ gives $F$, that is,
$\mathrm{id} \circ F = F$. -/
lemma id_comp (F : RegularFunction k σ τ) : (id k τ).comp F = F := by
  funext j
  simp

/-- **The identity is a right unit for composition.** For every regular function $F$ from
$k^\sigma$ to $k^\tau$, composing $F$ with the identity regular function on $k^\sigma$, whose
components are the variables $X_s$ for $s \in \sigma$, gives $F$, that is,
$F \circ \mathrm{id} = F$. -/
lemma comp_id (F : RegularFunction k σ τ) : F.comp (id k σ) = F := by
  funext j
  simp only [comp_apply]
  have hid : (id k σ : σ → MvPolynomial σ k) = MvPolynomial.X :=
    funext fun i => id_apply (k := k) i
  rw [hid, MvPolynomial.bind₁_X_left]
  rfl

/-- **Associativity of composition of regular functions.** For regular functions $H$ from
$k^\iota$ to $k^\kappa$, $G$ from $k^\tau$ to $k^\iota$ and $F$ from $k^\sigma$ to $k^\tau$,
we have $(H \circ G) \circ F = H \circ (G \circ F)$. -/
lemma comp_assoc (H : RegularFunction k ι κ) (G : RegularFunction k τ ι)
    (F : RegularFunction k σ τ) :
    (H.comp G).comp F = H.comp (G.comp F) := by
  funext i
  simp only [comp_apply]
  exact MvPolynomial.bind₁_bind₁ G F (H i)

/-- **Evaluation of a regular function at a point.** Let $k$ be a commutative semiring and let
$S$ be a commutative $k$-algebra. For a regular function $F$ from $k^\sigma$ to $k^\tau$ and a
point $a \in S^\sigma$, the evaluation of $F$ at $a$ is the point $F(a) \in S^\tau$ whose $t$-th
coordinate, for $t \in \tau$, is the value of the polynomial $F_t$ at $a$, obtained by
substituting $a_s$ for $X_s$ for every $s \in \sigma$. -/
noncomputable def aeval {σ τ : Type*} {S₁ : Type*} [CommSemiring S₁] [Algebra k S₁]
    (F : RegularFunction k σ τ) : (σ → S₁) → τ → S₁ :=
  fun a t ↦ MvPolynomial.aeval a (F t)

/-- **Evaluation respects composition.** Let $k$ be a commutative semiring and let $S$ be a
commutative $k$-algebra. For regular functions $G$ from $k^\tau$ to $k^\iota$ and $F$ from
$k^\sigma$ to $k^\tau$ and every point $a \in S^\sigma$, write $F(a) \in S^\tau$ for the
evaluation of $F$ at $a$. Then evaluating the composition $G \circ F$ at $a$ gives $G(F(a))$,
the evaluation of $G$ at the point $F(a)$. -/
lemma comp_aeval
    {σ τ ι S₁ : Type*} [CommSemiring S₁] [Algebra k S₁]
    (G : RegularFunction k τ ι) (F : RegularFunction k σ τ)
    (a : σ → S₁) : (G.comp F).aeval a = G.aeval (F.aeval a) := by
  ext i
  rw [aeval, comp, MvPolynomial.aeval_bind₁, ←aeval]
  rfl

end RegularFunction

end MvPolynomial
