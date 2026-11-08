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

/-- The automorphism group `Aut R` of a rack `R`, as the subgroup of permutations `f` of `R`
with `f (x ◃ y) = f x ◃ f y` (Mathlib's `x ◃ y` is the paper's `s_x(y)`).

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

/-- Two virtual racks `(R₁, f₁)` and `(R₂, f₂)` are isomorphic: some bijective rack
homomorphism `ψ : R₁ ≃ R₂` intertwines the virtual structures, `ψ f₁ = f₂ ψ`.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 2.2 (virtual rack isomorphisms). -/
def VirtualRackIso {R₁ R₂ : Type*} [Rack R₁] [Rack R₂] (f₁ : Perm R₁) (f₂ : Perm R₂) : Prop :=
  ∃ ψ : R₁ ≃ R₂, (∀ x y, ψ (x ◃ y) = ψ x ◃ ψ y) ∧ ∀ x, ψ (f₁ x) = f₂ (ψ x)

/-- `v(R)`: the number of isomorphism classes of virtual racks with underlying rack `R`,
i.e. of virtual structures `f ∈ Aut R` modulo virtual rack isomorphism. (Every virtual rack
whose underlying rack is isomorphic to `R` is isomorphic to one of the form `(R, f)`.)

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 3.2.2 (the invariant `v(R)`). -/
noncomputable def virtualRackClassCount (R : Type*) [Rack R] : ℕ :=
  Nat.card (Quot fun f g : rackAut R => VirtualRackIso (f : Perm R) (g : Perm R))

/-- The affine transformation `T_{a,u} : x ↦ a + u x` of `ℤ/nℤ`, as a permutation of the
dihedral quandle `R_n`.

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

/-- Every rack automorphism is a virtual rack isomorphism from `(R, f)` to itself; in
particular virtual rack isomorphism is reflexive.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 2.2 (virtual rack isomorphisms). -/
theorem virtualRackIso_refl {R : Type*} [Rack R] (f : Perm R) : VirtualRackIso f f :=
  ⟨Equiv.refl R, fun _ _ => rfl, fun _ => rfl⟩

/-- `T_{a,u}` is a rack automorphism of the dihedral quandle `R_n`, i.e. a virtual structure.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 2.2 (virtual structures on the dihedral quandle). -/
theorem dihedralAffinePerm_mem_rackAut (n : ℕ) (a : ZMod n) (u : (ZMod n)ˣ) :
    dihedralAffinePerm n a u ∈ rackAut (Quandle.Dihedral n) := by
  change ∀ x y : ZMod n, _ = _
  intro x y
  change a + (u : ZMod n) * (2 * x - y) = 2 * (a + (u : ZMod n) * x) - (a + (u : ZMod n) * y)
  ring

/-- The action of `(ℤ/nℤ)ˣ` on `ℤ/nℤ` by multiplication, as automorphisms of the
multiplicative copy of `ℤ/nℤ`.

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

/-- The holomorph `G = A ⋊ A^×` of `A = ℤ/nℤ`; the element `(a, u)` is
`⟨Multiplicative.ofAdd a, u⟩`, with product `(a, u)(b, v) = (a + u b, u v)`.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Section 4. -/
abbrev cyclicHolomorph (n : ℕ) : Type :=
  Multiplicative (ZMod n) ⋊[zmodUnitsMulAut n] (ZMod n)ˣ

/-- The product in the holomorph: `(a, u)(b, v) = (a + u b, u v)`.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, proof of Proposition 22. -/
theorem cyclicHolomorph_mk_mul_mk (n : ℕ) (a b : ZMod n) (u v : (ZMod n)ˣ) :
    (⟨Multiplicative.ofAdd a, u⟩ : cyclicHolomorph n) * ⟨Multiplicative.ofAdd b, v⟩ =
      ⟨Multiplicative.ofAdd (a + (u : ZMod n) * b), u * v⟩ :=
  rfl

/-- Two virtual structures `f₁, f₂` on a rack `R` give isomorphic virtual racks if and only if
they are conjugate in `Aut R`.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Proposition 14 (`jis-2025-25.8.4-prop-14`). -/
public theorem_wanted virtualRackIso_iff_isConj {R : Type*} [Rack R] (f₁ f₂ : rackAut R) :
    VirtualRackIso (f₁ : Perm R) (f₂ : Perm R) ↔ IsConj f₁ f₂

/-- A group `G` has trivial center if and only if its group automorphisms are exactly the
quandle automorphisms of `Conj G` (as sets of permutations of `G`).

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Lemma 17 (`jis-2025-25.8.4-lem-17`), quoting Bardakov,
Nasybullov, and Singh, Corollary 2. -/
public theorem_wanted center_eq_bot_iff_mulAut_eq_rackAut_conj (G : Type*) [Group G] :
    Subgroup.center G = ⊥ ↔
      (MulAut.toPerm (M := G)).range = rackAut (Quandle.Conj G)

/-- For `n > 0`, the virtual dihedral quandles `(R_n, T_{a,u})` and `(R_n, T_{b,v})` are
isomorphic if and only if `u = v` and `b = y a + (1 - u) x` for some `x ∈ ℤ/nℤ` and
`y ∈ (ℤ/nℤ)ˣ`.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Proposition 21 (`jis-2025-25.8.4-prop-21`). -/
public theorem_wanted dihedral_virtualRackIso_iff (n : ℕ) (hn : 0 < n) (a b : ZMod n)
    (u v : (ZMod n)ˣ) :
    VirtualRackIso (dihedralAffinePerm n a u) (dihedralAffinePerm n b v) ↔
      u = v ∧ ∃ x : ZMod n, ∃ y : (ZMod n)ˣ, b = (y : ZMod n) * a + (1 - (u : ZMod n)) * x

/-- For `n > 0`, two elements `(a, u), (b, v)` of the holomorph `ℤ/nℤ ⋊ (ℤ/nℤ)ˣ` are conjugate
if and only if `u = v` and `a, b` lie in one orbit of the multiplication action of
`(ℤ/nℤ)ˣ` on `A / A_u`, where `A_u = (1 - u) A` is the ideal generated by `1 - u`.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Proposition 22 (`jis-2025-25.8.4-prop-22`). -/
public theorem_wanted cyclicHolomorph_isConj_iff (n : ℕ) (hn : 0 < n) (a b : ZMod n)
    (u v : (ZMod n)ˣ) :
    IsConj (⟨Multiplicative.ofAdd a, u⟩ : cyclicHolomorph n) ⟨Multiplicative.ofAdd b, v⟩ ↔
      u = v ∧ ∃ y : (ZMod n)ˣ,
        Ideal.Quotient.mk (Ideal.span {1 - (u : ZMod n)}) b =
          Ideal.Quotient.mk (Ideal.span {1 - (u : ZMod n)}) ((y : ZMod n) * a)

/-- For `n > 0`, the class number of the holomorph `ℤ/nℤ ⋊ (ℤ/nℤ)ˣ` is
`φ(n) ∑_{d ∣ n} 1/φ(d)`.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Theorem 23 (`jis-2025-25.8.4-thm-23`). -/
public theorem_wanted card_conjClasses_cyclicHolomorph (n : ℕ) (hn : 0 < n) :
    (Nat.card (ConjClasses (cyclicHolomorph n)) : ℚ) =
      n.totient * ∑ d ∈ n.divisors, (1 : ℚ) / d.totient

/-- For `n > 0`, the number of isomorphism classes of virtual quandles whose underlying quandle
is the dihedral quandle `R_n` is `v(R_n) = φ(n) ∑_{d ∣ n} 1/φ(d)`.

Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
Sequences 28 (2025), Article 25.8.4, Theorem 1 (`jis-2025-25.8.4-thm-1`). -/
public theorem_wanted virtualRackClassCount_dihedral (n : ℕ) (hn : 0 < n) :
    (virtualRackClassCount (Quandle.Dihedral n) : ℚ) =
      n.totient * ∑ d ∈ n.divisors, (1 : ℚ) / d.totient

end

end MetaMathlibExt
