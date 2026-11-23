/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Quandle
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.Nat.Totient
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span

namespace MetaMathlibExt

@[expose] public section

open Equiv Quandles

/-- **Automorphism group of a rack.** For a rack $R$ with operation $\triangleleft$, the
automorphism group $\operatorname{Aut} R$ is the subgroup of the group of permutations of $R$
consisting of the permutations $f$ with $f(x \triangleleft y) = f(x) \triangleleft f(y)$ for all
$x, y \in R$.

Here $x \triangleleft y$ is the paper's $s_x(y)$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 2.2 (rack homomorphisms and `Aut R`). -/
def rackAut (R : Type*) [Rack R] : Subgroup (Perm R) where
  carrier := {f | ∀ x y, f (x ◃ y) = f x ◃ f y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro f g hf hg x y
    simp only [Perm.mul_apply, hg x y, hf (g x) (g y)]
  inv_mem' := by
    intro f hf x y
    apply f.injective
    rw [hf (f⁻¹ x) (f⁻¹ y)]
    simp

/-- **Isomorphism of virtual racks.** Write $x \triangleleft y$ for the operation of a rack. A
virtual rack $(R, f)$ is a rack $R$ together with a rack automorphism $f$ of $R$, its virtual
structure. Let $R_1$ and $R_2$ be racks and let $f_1$ and $f_2$ be permutations of $R_1$ and
$R_2$. Then $(R_1, f_1)$ and $(R_2, f_2)$ are isomorphic when there is a bijection
$\psi \colon R_1 \to R_2$ such that $\psi(x \triangleleft y) = \psi(x) \triangleleft \psi(y)$
for all $x, y \in R_1$ and $\psi(f_1(x)) = f_2(\psi(x))$ for all $x \in R_1$.

The definition does not require $f_1$ and $f_2$ to be rack automorphisms; for virtual racks it
is the usual notion of isomorphism.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 2.2 (virtual rack isomorphisms). -/
def VirtualRackIso {R₁ R₂ : Type*} [Rack R₁] [Rack R₂] (f₁ : Perm R₁) (f₂ : Perm R₂) : Prop :=
  ∃ ψ : R₁ ≃ R₂, (∀ x y, ψ (x ◃ y) = ψ x ◃ ψ y) ∧ ∀ x, ψ (f₁ x) = f₂ (ψ x)

/-- **Number of isomorphism classes of virtual racks on a rack.** For a rack $R$, let
$\operatorname{Aut} R$ be its group of rack automorphisms; a virtual structure on $R$ is an
element $f \in \operatorname{Aut} R$, and $(R, f)$ is the corresponding virtual rack. The number
$v(R)$ is the number of classes of virtual structures on $R$, where $f, g \in \operatorname{Aut} R$
are identified when the virtual racks $(R, f)$ and $(R, g)$ are isomorphic; that is, the number
of isomorphism classes of virtual racks with underlying rack $R$. It is $0$ when there are
infinitely many classes.

Every virtual rack whose underlying rack is isomorphic to $R$ is isomorphic to one of the form
$(R, f)$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 3.2.2 (the invariant `v(R)`). -/
noncomputable def virtualRackClassCount (R : Type*) [Rack R] : ℕ :=
  Nat.card (Quot fun f g : rackAut R => VirtualRackIso (f : Perm R) (g : Perm R))

/-- **Affine permutations of the dihedral quandle.** For a natural number $n$, an element
$a \in \mathbb{Z}/n\mathbb{Z}$ and a unit $u \in (\mathbb{Z}/n\mathbb{Z})^\times$, $T_{a,u}$ is the
affine map $x \mapsto a + u x$ of $\mathbb{Z}/n\mathbb{Z}$, viewed as a permutation of the
dihedral quandle $R_n$ (the set $\mathbb{Z}/n\mathbb{Z}$ with $x \triangleleft y = 2x - y$).

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 2.2 (virtual structures on the dihedral quandle). -/
def dihedralAffinePerm (n : ℕ) (a : ZMod n) (u : (ZMod n)ˣ) : Perm (Quandle.Dihedral n) :=
  show Perm (ZMod n) from
  { toFun := fun x => a + (u : ZMod n) * x
    invFun := fun x => ((u⁻¹ : (ZMod n)ˣ) : ZMod n) * (x - a)
    left_inv := fun x => by
      simp only [add_sub_cancel_left, Units.inv_mul_cancel_left]
    right_inv := fun x => by
      simp only [Units.mul_inv_cancel_left, add_sub_cancel] }

/-- **Reflexivity of virtual rack isomorphism.** For every rack $R$ and every permutation $f$ of
$R$, the pair $(R, f)$ is isomorphic to itself in the sense of virtual rack isomorphism. The
permutation $f$ need not be a rack automorphism.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 2.2 (virtual rack isomorphisms). -/
theorem virtualRackIso_refl {R : Type*} [Rack R] (f : Perm R) : VirtualRackIso f f :=
  ⟨Equiv.refl R, fun _ _ => rfl, fun _ => rfl⟩

/-- **Affine maps are automorphisms of the dihedral quandle.** For every natural number $n$,
every $a \in \mathbb{Z}/n\mathbb{Z}$ and every unit $u \in (\mathbb{Z}/n\mathbb{Z})^\times$, the
affine map $T_{a,u} \colon x \mapsto a + u x$ is a rack automorphism of the dihedral quandle
$R_n$, the set $\mathbb{Z}/n\mathbb{Z}$ with $x \triangleleft y = 2x - y$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 2.2 (virtual structures on the dihedral quandle). -/
theorem dihedralAffinePerm_mem_rackAut (n : ℕ) (a : ZMod n) (u : (ZMod n)ˣ) :
    dihedralAffinePerm n a u ∈ rackAut (Quandle.Dihedral n) := by
  change ∀ x y : ZMod n, _ = _
  intro x y
  change a + (u : ZMod n) * (2 * x - y) = 2 * (a + (u : ZMod n) * x) - (a + (u : ZMod n) * y)
  ring

/-- **Multiplication action of the units of $\mathbb{Z}/n\mathbb{Z}$.** For a natural number
$n$, the group homomorphism from the unit group $(\mathbb{Z}/n\mathbb{Z})^\times$ to the
automorphism group of the additive group $\mathbb{Z}/n\mathbb{Z}$ that sends a unit $u$ to
multiplication by $u$, the automorphism $x \mapsto u x$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 4 (the holomorph `A ⋊ A^×`, `A = ℤ/nℤ`). -/
def zmodUnitsMulAut (n : ℕ) : (ZMod n)ˣ →* MulAut (Multiplicative (ZMod n)) where
  toFun u :=
    { toFun := fun x => Multiplicative.ofAdd ((u : ZMod n) * x.toAdd)
      invFun := fun x => Multiplicative.ofAdd (((u⁻¹ : (ZMod n)ˣ) : ZMod n) * x.toAdd)
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_mul' := fun x y => by simp [mul_add] }
  map_one' := by ext; simp
  map_mul' := fun u v => by ext; simp [mul_assoc]

/-- **Holomorph of $\mathbb{Z}/n\mathbb{Z}$.** For a natural number $n$, let
$A = \mathbb{Z}/n\mathbb{Z}$. The holomorph of $A$ is the semidirect product $A \rtimes A^\times$
in which the unit group $A^\times$ acts on $A$ by multiplication. Its elements are the pairs
$(a, u)$ with $a \in A$ and $u \in A^\times$, with product $(a, u)(b, v) = (a + u b, u v)$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 4. -/
abbrev cyclicHolomorph (n : ℕ) : Type :=
  Multiplicative (ZMod n) ⋊[zmodUnitsMulAut n] (ZMod n)ˣ

/-- **Multiplication in the holomorph of $\mathbb{Z}/n\mathbb{Z}$.** For a natural number $n$, let
$A = \mathbb{Z}/n\mathbb{Z}$ and write $(a, u)$ for the element of the holomorph
$A \rtimes A^\times$ with $a \in A$ and $u \in A^\times$. For all $a, b \in A$ and
$u, v \in A^\times$, $(a, u)(b, v) = (a + u b, u v)$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, proof of Proposition 22. -/
theorem cyclicHolomorph_mk_mul_mk (n : ℕ) (a b : ZMod n) (u v : (ZMod n)ˣ) :
    (⟨Multiplicative.ofAdd a, u⟩ : cyclicHolomorph n) * ⟨Multiplicative.ofAdd b, v⟩ =
      ⟨Multiplicative.ofAdd (a + (u : ZMod n) * b), u * v⟩ :=
  rfl

/-- **Isomorphism of virtual structures is conjugacy.** Let $R$ be a rack and let $f_1$ and $f_2$
be elements of its automorphism group $\operatorname{Aut} R$. Then the virtual racks $(R, f_1)$
and $(R, f_2)$ are isomorphic if and only if $f_1$ and $f_2$ are conjugate in
$\operatorname{Aut} R$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Proposition 14 (`jis-2025-25.8.4-prop-14`). -/
public theorem_wanted virtualRackIso_iff_isConj {R : Type*} [Rack R] (f₁ f₂ : rackAut R) :
    VirtualRackIso (f₁ : Perm R) (f₂ : Perm R) ↔ IsConj f₁ f₂

/-- **Trivial center and automorphisms of the conjugation quandle.** For a group $G$, let
$\operatorname{Conj}(G)$ be the conjugation quandle on $G$, with $x \triangleleft y = x y x^{-1}$.
Then $G$ has trivial center if and only if the permutations of $G$ that are group automorphisms
are exactly the rack automorphisms of $\operatorname{Conj}(G)$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Lemma 17 (`jis-2025-25.8.4-lem-17`), quoting Bardakov,
Nasybullov, and Singh, Corollary 2. -/
public theorem_wanted center_eq_bot_iff_mulAut_eq_rackAut_conj (G : Type*) [Group G] :
    Subgroup.center G = ⊥ ↔
      (MulAut.toPerm (M := G)).range = rackAut (Quandle.Conj G)

/-- **Isomorphism of affine virtual dihedral quandles.** Let $n > 0$, let $R_n$ be the dihedral
quandle on $\mathbb{Z}/n\mathbb{Z}$ (with $x \triangleleft y = 2x - y$), and for
$a \in \mathbb{Z}/n\mathbb{Z}$ and $u \in (\mathbb{Z}/n\mathbb{Z})^\times$ let $T_{a,u}$ be the
permutation $x \mapsto a + u x$ of $R_n$. For all $a, b \in \mathbb{Z}/n\mathbb{Z}$ and
$u, v \in (\mathbb{Z}/n\mathbb{Z})^\times$, the virtual racks $(R_n, T_{a,u})$ and
$(R_n, T_{b,v})$ are isomorphic if and only if $u = v$ and $b = y a + (1 - u) x$ for some
$x \in \mathbb{Z}/n\mathbb{Z}$ and $y \in (\mathbb{Z}/n\mathbb{Z})^\times$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Proposition 21 (`jis-2025-25.8.4-prop-21`). -/
public theorem_wanted dihedral_virtualRackIso_iff (n : ℕ) (hn : 0 < n) (a b : ZMod n)
    (u v : (ZMod n)ˣ) :
    VirtualRackIso (dihedralAffinePerm n a u) (dihedralAffinePerm n b v) ↔
      u = v ∧ ∃ x : ZMod n, ∃ y : (ZMod n)ˣ, b = (y : ZMod n) * a + (1 - (u : ZMod n)) * x

/-- **Conjugacy in the holomorph of $\mathbb{Z}/n\mathbb{Z}$.** Let $n > 0$, let
$A = \mathbb{Z}/n\mathbb{Z}$, and write $(a, u)$ for the element of the holomorph
$A \rtimes A^\times$ with $a \in A$ and $u \in A^\times$. Two elements $(a, u)$ and $(b, v)$ are
conjugate if and only if $u = v$ and there is a unit $y \in A^\times$ with $b \equiv y a$ modulo
the ideal $(1 - u)A$ generated by $1 - u$.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Proposition 22 (`jis-2025-25.8.4-prop-22`). -/
public theorem_wanted cyclicHolomorph_isConj_iff (n : ℕ) (hn : 0 < n) (a b : ZMod n)
    (u v : (ZMod n)ˣ) :
    IsConj (⟨Multiplicative.ofAdd a, u⟩ : cyclicHolomorph n) ⟨Multiplicative.ofAdd b, v⟩ ↔
      u = v ∧ ∃ y : (ZMod n)ˣ,
        Ideal.Quotient.mk (Ideal.span {1 - (u : ZMod n)}) b =
          Ideal.Quotient.mk (Ideal.span {1 - (u : ZMod n)}) ((y : ZMod n) * a)

/-- **Class number of the holomorph of $\mathbb{Z}/n\mathbb{Z}$.** For every integer $n > 0$,
the number of conjugacy classes of the holomorph
$\mathbb{Z}/n\mathbb{Z} \rtimes (\mathbb{Z}/n\mathbb{Z})^\times$ of $\mathbb{Z}/n\mathbb{Z}$ equals
$\varphi(n) \sum_{d \mid n} 1/\varphi(d)$, where $\varphi$ is Euler's totient function.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Theorem 23 (`jis-2025-25.8.4-thm-23`). -/
public theorem_wanted card_conjClasses_cyclicHolomorph (n : ℕ) (hn : 0 < n) :
    (Nat.card (ConjClasses (cyclicHolomorph n)) : ℚ) =
      n.totient * ∑ d ∈ n.divisors, (1 : ℚ) / d.totient

/-- **Virtual quandle structures on the dihedral quandle.** For every $n > 0$, the number
$v(R_n)$ of isomorphism classes of virtual racks whose underlying rack is the dihedral quandle
$R_n$ (the set $\mathbb{Z}/n\mathbb{Z}$ with $x \triangleleft y = 2x - y$) equals
$\varphi(n) \sum_{d \mid n} 1/\varphi(d)$, where $\varphi$ is Euler's totient function.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Theorem 1 (`jis-2025-25.8.4-thm-1`). -/
public theorem_wanted virtualRackClassCount_dihedral (n : ℕ) (hn : 0 < n) :
    (virtualRackClassCount (Quandle.Dihedral n) : ℚ) =
      n.totient * ∑ d ∈ n.divisors, (1 : ℚ) / d.totient

end

end MetaMathlibExt
