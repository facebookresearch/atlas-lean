/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.BrauerCorestriction

/-!
# Transversal words and the native corestriction formula

On `ℤ/4` with the subgroup `{0, 2}` and the transversal `{0, 1}`, the word of
the identity coset and the generator is the nontrivial subgroup element `2`,
while the naive conjugate without the translated index `g⁻¹ • u` leaves the
subgroup. For the trivial extension `K/K` the fixing subgroup is everything,
the finite-field dictionary is inhabited by identities, and with the trivial
transversal the transfer formula returns the original cocycle values.
-/

noncomputable section

namespace MathlibExtTest.BrauerCorestriction

open AlgebraicGeometry.BrauerCoefficients AlgebraicGeometry.BrauerCorestriction

/-! ## Words for an arbitrary transversal -/

section Generic

variable {H : Type*} [Group H] (V : Subgroup H) (s : H ⧸ V → H)

example (u : H ⧸ V) (g : H) : transversalWord V s u g = (s u)⁻¹ * g * s (g⁻¹ • u) := rfl

/-- The word of the identity is trivial for every choice of representatives. -/
theorem transversalWord_one (u : H ⧸ V) : transversalWord V s u 1 = 1 := by
  simp [transversalWord]

/-- The cocycle identity gives inverse words. -/
example (u : H ⧸ V) (g : H) :
    transversalWord V s u g * transversalWord V s (g⁻¹ • u) g⁻¹ = 1 := by
  rw [transversalWord_mul, mul_inv_cancel, transversalWord_one]

/-- For the trivial subgroup, every transversal word is the identity. -/
example (s : H ⧸ (⊥ : Subgroup H) → H)
    (hs : ∀ u, (QuotientGroup.mk (s u) : H ⧸ (⊥ : Subgroup H)) = u)
    (u : H ⧸ (⊥ : Subgroup H)) (g : H) : transversalWord ⊥ s u g = 1 :=
  Subgroup.mem_bot.mp (transversalWord_mem ⊥ s hs u g)

end Generic

/-! ## A concrete transversal of `{0, 2}` in `ℤ/4` -/

private abbrev G := Multiplicative (ZMod 4)

/-- Reduction modulo two; its kernel is `{0, 2}`. -/
private def red : G →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom

private abbrev U : Subgroup G := red.ker

/-- The transversal `{0, 1}`. -/
private def t (u : G ⧸ U) : G :=
  Multiplicative.ofAdd
    ((Multiplicative.toAdd (QuotientGroup.kerLift red u)).val : ZMod 4)

private theorem t_section : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u := by
  intro u
  induction u using QuotientGroup.induction_on with
  | H g =>
    rw [QuotientGroup.eq, MonoidHom.mem_ker]
    revert g
    decide

example : t (QuotientGroup.mk (Multiplicative.ofAdd 3)) = Multiplicative.ofAdd 1 := by
  decide

/-- The word of the identity coset and the generator is `2`, not `0`. -/
example : transversalWord U t (QuotientGroup.mk 1) (Multiplicative.ofAdd 1) =
    Multiplicative.ofAdd 2 := by
  decide

example : transversalWord U t (QuotientGroup.mk 1) (Multiplicative.ofAdd 1) ∈ U :=
  transversalWord_mem U t t_section _ _

/-- Omitting the translated index `g⁻¹ • u` leaves the subgroup. -/
example : (t (QuotientGroup.mk 1))⁻¹ * Multiplicative.ofAdd 1 * t (QuotientGroup.mk 1) ∉ U := by
  rw [MonoidHom.mem_ker]
  decide

example (g h : G) (u : G ⧸ U) :
    transversalWord U t u g * transversalWord U t (g⁻¹ • u) h = transversalWord U t u (g * h) :=
  transversalWord_mul U t u g h

/-! ## The trivial extension `K/K` -/

variable (K : Type) [Field K]

private abbrev σK : K →ₐ[K] SeparableClosure K := Algebra.ofId K (SeparableClosure K)

/-- The image of `K` is fixed by every absolute Galois automorphism. -/
theorem mem_fixingSubgroup_self (g : Field.absoluteGaloisGroup K) :
    g ∈ fixingSubgroup K K (σK K) := by
  rintro ⟨y, hy⟩
  obtain ⟨a, rfl⟩ := AlgHom.mem_fieldRange.mp hy
  exact g.commutes a

example : fixingSubgroup K K (σK K) = ⊤ :=
  eq_top_iff.mpr fun g _ => mem_fixingSubgroup_self K g

instance : Subsingleton (Field.absoluteGaloisGroup K ⧸ fixingSubgroup K K (σK K)) :=
  ⟨fun a b => by
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    exact QuotientGroup.eq.mpr (mem_fixingSubgroup_self K _)⟩

/-- The finite-field dictionary is inhabited by identities for `K/K`. -/
def trivialPair : FiniteFieldPair K K (σK K) where
  closure := RingEquiv.refl _
  closure_base _ := rfl
  galois :=
    { toFun g := ⟨g, mem_fixingSubgroup_self K g⟩
      invFun g := g.val
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }
  equivariant _ _ := rfl
  finite_cosets := inferInstance
  open_subgroup := by
    rw [Set.eq_univ_of_forall (mem_fixingSubgroup_self K)]
    exact isOpen_univ

theorem trivialPair_galois_symm (g : fixingSubgroup K K (σK K)) :
    (trivialPair K).galois.symm g = g.val := rfl

theorem transportUnits_trivialPair (u : SepUnits K) :
    transportUnits K K (σK K) (trivialPair K) u = u := rfl

theorem unitAction_one (u : SepUnits K) : unitAction K 1 u = u := by
  rw [← unitsRep_action, map_one]
  rfl

/-- Any coset is represented by the identity. -/
theorem one_section (u : Field.absoluteGaloisGroup K ⧸ fixingSubgroup K K (σK K)) :
    (QuotientGroup.mk 1 : Field.absoluteGaloisGroup K ⧸ fixingSubgroup K K (σK K)) = u :=
  Subsingleton.elim _ _

/-- With the trivial transversal, the transfer formula for `K/K` is the identity
on actual cocycle values: no stray conjugation or coefficient twist. -/
example (c : TwoCocycles K) (g h : Field.absoluteGaloisGroup K) :
    transferValue K K (σK K) (trivialPair K) (fun _ => 1) (one_section K) c g h =
      inhomogeneousValue K c g h := by
  have : Unique (Field.absoluteGaloisGroup K ⧸ fixingSubgroup K K (σK K)) :=
    uniqueOfSubsingleton (QuotientGroup.mk 1)
  simp only [transferValue, Fintype.sum_unique, transversalWord, inv_one, one_mul, mul_one,
    trivialPair_galois_symm, transportUnits_trivialPair, unitAction_one]

/-! ## The general formula -/

variable (L : Type) [Field L] [Algebra K L] (σ : L →ₐ[K] SeparableClosure K)
  (P : FiniteFieldPair K L σ)
  (s : Field.absoluteGaloisGroup K ⧸ fixingSubgroup K L σ → Field.absoluteGaloisGroup K)
  (hs : ∀ u, (QuotientGroup.mk (s u) : Field.absoluteGaloisGroup K ⧸ fixingSubgroup K L σ) = u)

example (u : (SeparableClosure L)ˣ) :
    ((Additive.toMul (transportUnits K L σ P (Additive.ofMul u)) : (SeparableClosure K)ˣ) :
      SeparableClosure K) = P.closure u := rfl

theorem transferValue_zero (g h : Field.absoluteGaloisGroup K) :
    transferValue K L σ P s hs 0 g h = 0 := by
  simp [transferValue]

/-- A normalized corestriction sends the zero cocycle to a cocycle with zero values. -/
example (cor : NormalizedCorestriction K L σ P) :
    ∃ d : TwoCocycles K, (∀ g h, inhomogeneousValue K d g h = 0) ∧
      cor.val (cocycleClass L 0) = cocycleClass K d := by
  obtain ⟨d, hd, hcls⟩ := cor.2 s hs 0
  exact ⟨d, fun g h => (hd g h).trans (transferValue_zero K L σ P s hs g h), hcls⟩

end MathlibExtTest.BrauerCorestriction
