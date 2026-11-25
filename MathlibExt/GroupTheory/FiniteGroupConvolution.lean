/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

open scoped BigOperators

namespace MathlibExt.GroupTheory.FiniteGroupConvolutionWanted

/-!
# Convolution of functions on a finite group

The convolution product on complex-valued functions on a finite group, with
its monoid structure and the Fourier-side diagonalization: pairing the
convolution against a one-dimensional character splits as a product.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "convolution" (reference-only, no Lean formalization);
A. Terras, Fourier Analysis on Finite Groups and Applications, Ch. 1–2
(convolution on finite groups and its Fourier transform).
-/

/-- **Convolution on a finite group.** For a finite group $G$ and functions
$f, g : G \to \mathbb{C}$, the convolution $f \ast g : G \to \mathbb{C}$ is defined by
$(f \ast g)(x) = \sum_{y \in G} f(y)\, g(y^{-1} x)$ for $x \in G$. -/
def conv {G : Type*} [Group G] [Fintype G] (f g : G → ℂ) : G → ℂ :=
  fun x => ∑ y : G, f y * g (y⁻¹ * x)

private theorem conv_assoc_inner {G : Type*} [Group G] [Fintype G]
    (g h : G → ℂ) (z x : G) :
    (∑ y : G, g (z⁻¹ * y) * h (y⁻¹ * x)) =
      ∑ w : G, g w * h (w⁻¹ * (z⁻¹ * x)) := by
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun w => ?_
  simp [mul_assoc]

private theorem conv_assoc_apply {G : Type*} [Group G] [Fintype G]
    (f g h : G → ℂ) (x : G) : conv (conv f g) h x = conv f (conv g h) x := by
  simp only [conv]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, conv_assoc_inner]

/--
**Associativity of convolution.** Let $G$ be a finite group and write $f \ast g$ for the
convolution $(f \ast g)(x) = \sum_{y \in G} f(y)\, g(y^{-1} x)$ of functions on $G$. For all
$f, g, h : G \to \mathbb{C}$ we have $(f \ast g) \ast h = f \ast (g \ast h)$.

Proof: Expand into double sums, swap them, and reindex by left multiplication,
following the finite group-algebra argument in Terras, Ch. 1.

Proves `Wanted` entry `conv_assoc`.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "convolution"; A. Terras, Fourier Analysis on Finite Groups and
Applications, Ch. 1 (the group algebra).
-/
public theorem conv_assoc {G : Type*} [Group G] [Fintype G]
    (f g h : G → ℂ) : conv (conv f g) h = conv f (conv g h) := by
  funext x
  exact conv_assoc_apply f g h x

private theorem conv_single_one_apply {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (f : G → ℂ) (x : G) :
    conv (Pi.single (1 : G) (1 : ℂ)) f x = f x := by
  simp [conv, Pi.single_apply]

/--
**The delta function at the identity is a left unit for convolution.** Let $G$ be a finite group,
write $f \ast g$ for the convolution $(f \ast g)(x) = \sum_{y \in G} f(y)\, g(y^{-1} x)$ of
functions on $G$, and let $\delta_1 : G \to \mathbb{C}$ be given by $\delta_1(1) = 1$ and
$\delta_1(x) = 0$ for $x \neq 1$. Then $\delta_1 \ast f = f$ for every $f : G \to \mathbb{C}$.

Proof: Expand the convolution and collapse the sum at the unique nonzero value
of the delta function, following the identity-element argument in Terras, Ch. 1.

Proves `Wanted` entry `conv_single_one`.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "convolution"; A. Terras, Fourier Analysis on Finite Groups and
Applications, Ch. 1 (identity of the group algebra).
-/
public theorem conv_single_one {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (f : G → ℂ) : conv (Pi.single (1 : G) (1 : ℂ)) f = f := by
  funext x
  exact conv_single_one_apply f x

private theorem conv_comm_apply {G : Type*} [CommGroup G] [Fintype G]
    (f g : G → ℂ) (x : G) : conv f g x = conv g f x := by
  simp only [conv]
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x)) _ _ fun y => ?_
  simp [mul_comm]

/--
**Convolution on a finite abelian group is commutative.** Let $G$ be a finite abelian group and
write $f \ast g$ for the convolution $(f \ast g)(x) = \sum_{y \in G} f(y)\, g(y^{-1} x)$ of
functions on $G$. For all $f, g : G \to \mathbb{C}$ we have $f \ast g = g \ast f$.

Proof: Reindex by $y \mapsto y^{-1} x$ and use commutativity in $G$ and in $\mathbb{C}$,
as in the commutative group-algebra argument in Terras, Ch. 2.

Proves `Wanted` entry `conv_comm_of_comm`.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "convolution"; A. Terras, Fourier Analysis on Finite Groups and
Applications, Ch. 2 (commutative group algebra of an abelian group).
-/
public theorem conv_comm_of_comm {G : Type*} [CommGroup G] [Fintype G]
    (f g : G → ℂ) : conv f g = conv g f := by
  funext x
  exact conv_comm_apply f g x

private theorem conv_charPair_inner {G : Type*} [Group G] [Fintype G]
    (φ : G →* ℂ) (g : G → ℂ) (y : G) :
    (∑ x : G, φ x * g (y⁻¹ * x)) = φ y * ∑ z : G, φ z * g z := by
  rw [← Equiv.sum_comp (Equiv.mulLeft y)]
  simp [map_mul, Finset.mul_sum, mul_assoc]

private theorem conv_charPair_apply {G : Type*} [Group G] [Fintype G]
    (φ : G →* ℂ) (f g : G → ℂ) :
    (∑ x : G, φ x * conv f g x) =
      (∑ x : G, φ x * f x) * (∑ x : G, φ x * g x) := by
  simp only [conv]
  rw [Fintype.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  calc
    (∑ x : G, φ x * (f y * g (y⁻¹ * x))) =
        f y * ∑ x : G, φ x * g (y⁻¹ * x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ac_rfl
    _ = f y * (φ y * ∑ z : G, φ z * g z) := by rw [conv_charPair_inner]
    _ = ∑ z : G, (φ y * f y) * (φ z * g z) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ac_rfl

/--
**Convolution theorem for one-dimensional characters.** Let $G$ be a finite group, let
$\varphi : G \to \mathbb{C}$ satisfy $\varphi(1) = 1$ and $\varphi(xy) = \varphi(x)\varphi(y)$
for all $x, y \in G$ (a one-dimensional character), and let $f, g : G \to \mathbb{C}$. Writing
$f \ast g$ for the convolution $(f \ast g)(x) = \sum_{y \in G} f(y)\, g(y^{-1} x)$, we have
$$
\sum_{x \in G} \varphi(x)\,(f \ast g)(x) =
\Big(\sum_{x \in G} \varphi(x) f(x)\Big)\Big(\sum_{x \in G} \varphi(x) g(x)\Big).
$$

Proof: Swap the finite sums, reindex by $x = yz$, and use multiplicativity of $\varphi$ to
factor the character pairing, following Terras, Ch. 2–3.

Proves `Wanted` entry `charPair_conv`.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "convolution"; A. Terras, Fourier Analysis on Finite Groups and
Applications, Ch. 2–3 (the Fourier transform takes convolution to pointwise
products).
-/
public theorem charPair_conv {G : Type*} [Group G] [Fintype G]
    (φ : G →* ℂ) (f g : G → ℂ) :
    (∑ x : G, φ x * conv f g x) =
      (∑ x : G, φ x * f x) * (∑ x : G, φ x * g x) := by
  exact conv_charPair_apply φ f g

end MathlibExt.GroupTheory.FiniteGroupConvolutionWanted
