/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.HopfAlgebra.HopfKer
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

@[expose] public section

open scoped TensorProduct

namespace HopfAlgebra

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]
  {B : Type w} [CommRing B] [Bialgebra R B]

/-- Consumer with the original binders: membership in the Hopf kernel is the
coaction fixed-point condition. -/
theorem exactSource_hopfKer (π : A →ₐc[R] B) (a : A) :
    a ∈ hopfKer π ↔ coaction π a = a ⊗ₜ[R] 1 :=
  mem_hopfKer_iff π a

example (π : A →ₐc[R] B) : (1 : A) ∈ hopfKer π := one_mem _

example (π : A →ₐc[R] B) (a a' : A) :
    canMap π (a ⊗ₜ[R] a') = (a ⊗ₜ[R] (1 : B)) * coaction π a' :=
  canMap_tmul π a a'

example (π : A →ₐc[R] B) : canMap π (1 ⊗ₜ[R] (1 : A)) = 1 ⊗ₜ[R] (1 : B) :=
  canMap_tmul_one π 1

noncomputable example {R' : Type u} [CommRing R'] {A' : Type v} [CommRing A'] [HopfAlgebra R' A']
    {B' : Type w} [CommRing B'] [HopfAlgebra R' B'] (π : A' →ₐc[R'] B')
    [Coalgebra.IsCocomm R' A'] [Module.Flat R' A'] [Module.Flat R' B']
    [Module.Flat R' ↥(hopfKer π)] : HopfAlgebra R' ↥(hopfKer π) := inferInstance

example {R' : Type u} [CommRing R'] {A' : Type v} [CommRing A'] [HopfAlgebra R' A']
    {B' : Type w} [CommRing B'] [HopfAlgebra R' B'] (π : A' →ₐc[R'] B')
    [Coalgebra.IsCocomm R' A'] [Module.Flat R' A'] [Module.Flat R' B']
    [Module.Flat R' ↥(hopfKer π)] : Coalgebra.IsCocomm R' ↥(hopfKer π) := by infer_instance

example {R' : Type u} [CommRing R'] {A' : Type v} [CommRing A'] [HopfAlgebra R' A']
    {B' : Type w} [CommRing B'] [HopfAlgebra R' B'] (π : A' →ₐc[R'] B')
    [Coalgebra.IsCocomm R' A'] [Module.Flat R' A'] [Module.Flat R' B']
    [Module.Flat R' ↥(hopfKer π)] (s : ↥(hopfKer π)) :
    ((antipode R' s : ↥(hopfKer π)) : A') = antipode R' (s : A') :=
  HopfKerHopf.coe_antipode π s

/-- Higher-universe consumer: the same statement in a larger universe. -/
example {R' : Type (u + 1)} [CommRing R'] {A' : Type (v + 1)} [CommRing A']
    [Bialgebra R' A'] {B' : Type (w + 1)} [CommRing B'] [Bialgebra R' B']
    (π : A' →ₐc[R'] B') (a : A') :
    a ∈ hopfKer π ↔ coaction π a = a ⊗ₜ[R'] 1 :=
  mem_hopfKer_iff π a

example {H : Type v} [CommRing H] [HopfAlgebra R H] (I : Ideal H) [I.IsHopfIdeal R] :
    Function.Surjective (Bialgebra.Quotient.mkBialgHom (R := R) I) :=
  Ideal.Quotient.mk_surjective

example {H : Type v} [CommRing H] [HopfAlgebra R H] {I J : Ideal H}
    [I.IsHopfIdeal R] [J.IsHopfIdeal R] (h : I ≤ J) :
    Function.Surjective (quotientFactorBialgHom (R := R) h) :=
  quotientFactorBialgHom_surjective h

end HopfAlgebra

/-! Concrete checks of the coinvariant, balancing and Hopf–Galois conditions. -/

namespace HopfKerTest

open HopfAlgebra

/-! ### The Hopf kernels of the identity and of the counit -/

section Extremes

/-- For the identity map, whose coaction is the comultiplication, the coinvariants are the
scalars: applying `ε ⊗ id` to `Δ a = a ⊗ 1` gives `a = ε a • 1`. -/
private theorem hopfKer_bialgHomId {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A] :
    hopfKer (BialgHom.id R A) = ⊥ := by
  refine le_antisymm (fun a ha => ?_) bot_le
  have h := congrArg (fun z => TensorProduct.lid R A (Coalgebra.counit.rTensor A z))
    (show coaction (BialgHom.id R A) a = a ⊗ₜ[R] 1 from ha)
  simp only [coaction_apply, BialgHom.id_toAlgHom, Algebra.TensorProduct.map_id, AlgHom.coe_id,
    id_eq, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul,
    LinearMap.rTensor_tmul] at h
  rw [h]
  exact Subalgebra.smul_mem _ (one_mem _) _

/-- Every element is coinvariant for the counit of a bialgebra: `(id ⊗ ε) (Δ a) = a ⊗ 1`. -/
private theorem mem_hopfKer_counitBialgHom {R A : Type*} [CommRing R] [CommRing A]
    [Bialgebra R A] (a : A) : a ∈ hopfKer (Bialgebra.counitBialgHom R A) := by
  rw [mem_hopfKer_iff, coaction_apply, ← Coalgebra.lTensor_counit_comul a]
  induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

example {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A] :
    hopfKer (Bialgebra.counitBialgHom R A) = ⊤ :=
  eq_top_iff.mpr fun a _ => mem_hopfKer_counitBialgHom a

end Extremes

/-! ### The group algebra of the cyclic group of order two -/

section CyclicGroupOfOrderTwo

open MonoidAlgebra

/-- The nonidentity element of the cyclic group of order two. -/
private abbrev gen : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

private theorem gen_ne_one : gen ≠ 1 := by decide

/-- In `k[C₂]`, `g ⊗ g ≠ g ⊗ 1` for the basis element `g` of the nonidentity element: applying
`ε ⊗ id` to both sides would give `g = 1`. -/
private theorem single_gen_tmul_single_gen_ne {k : Type*} [CommRing k] [Nontrivial k] :
    single gen (1 : k) ⊗ₜ[k] single gen (1 : k) ≠
      single gen (1 : k) ⊗ₜ[k] (1 : MonoidAlgebra k (Multiplicative (ZMod 2))) := by
  intro h
  have := congrArg (fun z => TensorProduct.lid k _ (Coalgebra.counit.rTensor _ z)) h
  simp only [LinearMap.rTensor_tmul, isGroupLikeElem_single_one, IsGroupLikeElem.counit_eq_one,
    TensorProduct.lid_tmul, one_smul] at this
  exact gen_ne_one ((single_left_inj one_ne_zero).mp (this.trans one_def))

/-- Positive membership: `g` is coinvariant for the counit `k[C₂] → k`, since its coaction is
`g ⊗ ε g = g ⊗ 1`. -/
private theorem single_gen_mem_hopfKer_counit {k : Type*} [CommRing k] :
    single gen (1 : k) ∈
      hopfKer (Bialgebra.counitBialgHom k (MonoidAlgebra k (Multiplicative (ZMod 2)))) := by
  rw [mem_hopfKer_iff, coaction_apply, (isGroupLikeElem_single_one gen).comul_eq_tmul_self,
    Algebra.TensorProduct.map_tmul]
  simp

/-- Negative membership: `g` is not coinvariant for the identity map, whose coaction is the
comultiplication: `Δ g = g ⊗ g ≠ g ⊗ 1`. Membership is read straight from the definition of
`hopfKer` as an equalizer, not through `mem_hopfKer_iff`. -/
example {k : Type*} [CommRing k] [Nontrivial k] :
    single gen (1 : k) ∉ hopfKer (BialgHom.id k (MonoidAlgebra k (Multiplicative (ZMod 2)))) := by
  intro h
  have h' : coaction (BialgHom.id k _) (single gen (1 : k)) = single gen (1 : k) ⊗ₜ[k] 1 := h
  rw [coaction_apply, (isGroupLikeElem_single_one gen).comul_eq_tmul_self,
    Algebra.TensorProduct.map_tmul] at h'
  exact single_gen_tmul_single_gen_ne (by simpa using h')

/-- The balancing relation `(1 * g) ⊗ 1 - 1 ⊗ (g * 1) = g ⊗ 1 - 1 ⊗ g` of the coinvariant `g` is
killed by the canonical map of the counit. -/
example {k : Type*} [CommRing k] :
    canMap (Bialgebra.counitBialgHom k (MonoidAlgebra k (Multiplicative (ZMod 2))))
      (single gen 1 ⊗ₜ[k] 1 - 1 ⊗ₜ[k] single gen 1) = 0 := by
  refine canMap_eq_zero_of_mem_span _ (Submodule.subset_span ⟨1, single gen 1, 1,
    single_gen_mem_hopfKer_counit, ?_⟩)
  rw [one_mul, mul_one]

/-- For the identity map, where `g` is not coinvariant, the same element is not killed:
`canMap` sends it to `g ⊗ 1 - g ⊗ g ≠ 0`. So the balancing identity needs `h ∈ hopfKer π`. -/
example {k : Type*} [CommRing k] [Nontrivial k] :
    canMap (BialgHom.id k (MonoidAlgebra k (Multiplicative (ZMod 2))))
      (single gen 1 ⊗ₜ[k] 1 - 1 ⊗ₜ[k] single gen 1) ≠ 0 := by
  rw [map_sub, canMap_tmul_one, canMap_one_tmul, coaction_apply,
    (isGroupLikeElem_single_one gen).comul_eq_tmul_self, Algebra.TensorProduct.map_tmul,
    sub_ne_zero]
  simpa using single_gen_tmul_single_gen_ne.symm

/-- For the identity map the balancing relations all vanish, since its Hopf kernel consists of the
scalars; so the nonzero element `g ⊗ 1 - 1 ⊗ g` is not in their span. -/
example {k : Type*} [CommRing k] [Nontrivial k] :
    single gen (1 : k) ⊗ₜ[k] 1 - 1 ⊗ₜ[k] single gen 1 ∉ Submodule.span k
      (balancingRelations (BialgHom.id k (MonoidAlgebra k (Multiplicative (ZMod 2))))) := by
  rw [(Submodule.span_eq_bot (R := k)).mpr ?_, Submodule.mem_bot, sub_eq_zero]
  · intro h
    have := congrArg (fun z => TensorProduct.lid k _ (Coalgebra.counit.rTensor _ z)) h
    simp only [LinearMap.rTensor_tmul, isGroupLikeElem_single_one,
      IsGroupLikeElem.counit_eq_one, TensorProduct.lid_tmul, one_smul, Bialgebra.counit_one] at this
    exact gen_ne_one ((single_left_inj one_ne_zero).mp (this.symm.trans one_def))
  · rintro _ ⟨a, h, a', hh, rfl⟩
    rw [hopfKer_bialgHomId] at hh
    obtain ⟨r, rfl⟩ := Algebra.mem_bot.mp hh
    rw [mul_comm, ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul, sub_self]

/-- The unit `k → k[C₂]` is not Hopf–Galois: its canonical map takes values in the multiples of
`1 ⊗ 1`, so it misses `1 ⊗ g`. -/
example {k : Type*} [CommRing k] [Nontrivial k] :
    ¬ IsHopfGalois (Bialgebra.unitBialgHom k (MonoidAlgebra k (Multiplicative (ZMod 2)))) := by
  rintro ⟨hsurj, -⟩
  obtain ⟨z, hz⟩ := hsurj (1 ⊗ₜ single gen 1)
  let ψ : k ⊗[k] MonoidAlgebra k (Multiplicative (ZMod 2)) →ₗ[k] k :=
    Finsupp.lapply gen ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap ∘ₗ
      (TensorProduct.lid k _).toLinearMap
  have h0 : ∀ w, ψ (canMap (Bialgebra.unitBialgHom k _) w) = 0 := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a b =>
      have hab : a ⊗ₜ[k] b = (a * b) • ((1 : k) ⊗ₜ[k] (1 : k)) := by
        rw [← TensorProduct.smul_tmul_smul, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
      rw [hab, map_smul, canMap_tmul_one, map_smul]
      simp [ψ, one_def]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  have h1 : ψ (1 ⊗ₜ single gen 1) = 1 := by simp [ψ]
  exact one_ne_zero (h1.symm.trans (hz ▸ h0 z))

end CyclicGroupOfOrderTwo

/-! ### The counit of a bialgebra is Hopf–Galois -/

section Counit

private theorem canMap_counitBialgHom {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
    (z : A ⊗[R] A) :
    canMap (Bialgebra.counitBialgHom R A) z = LinearMap.mul' R A z ⊗ₜ[R] (1 : R) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [canMap_tmul, coaction_eq_of_mem _ (mem_hopfKer_counitBialgHom b),
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, LinearMap.mul'_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy, TensorProduct.add_tmul]

private theorem sub_mul'_tmul_one_mem_span {R A : Type*} [CommRing R] [CommRing A]
    [Bialgebra R A] (z : A ⊗[R] A) :
    z - LinearMap.mul' R A z ⊗ₜ[R] (1 : A) ∈
      Submodule.span R (balancingRelations (Bialgebra.counitBialgHom R A)) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    have hrel : (a * b) ⊗ₜ[R] (1 : A) - a ⊗ₜ[R] (b * 1) ∈
        balancingRelations (Bialgebra.counitBialgHom R A) :=
      ⟨a, b, 1, mem_hopfKer_counitBialgHom b, rfl⟩
    have := (Submodule.span R _).neg_mem (Submodule.subset_span hrel)
    rwa [mul_one, neg_sub, ← LinearMap.mul'_apply (R := R) (A := A)] at this
  | add x y hx hy =>
    rw [map_add, TensorProduct.add_tmul, add_sub_add_comm]
    exact add_mem hx hy

/-- The counit `A → R` of a commutative bialgebra is Hopf–Galois: its Hopf kernel is all of `A`,
its canonical map is `a ⊗ a' ↦ a a' ⊗ 1`, and the kernel of that map is spanned by the balancing
relations. -/
example {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A] :
    IsHopfGalois (Bialgebra.counitBialgHom R A) := by
  refine ⟨fun y => ?_, fun z hz => ?_⟩
  · induction y using TensorProduct.inductionOn with
    | tmul a r =>
      exact ⟨r • (a ⊗ₜ[R] (1 : A)), by
        rw [map_smul, canMap_tmul_one, ← TensorProduct.tmul_smul, smul_eq_mul, mul_one]⟩
    | add x y hx hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u + v, map_add _ _ _⟩
  · have hmul : LinearMap.mul' R A z = 0 := by
      have := congrArg (TensorProduct.rid R A) hz
      rwa [canMap_counitBialgHom, TensorProduct.rid_tmul, one_smul, map_zero] at this
    simpa [hmul] using sub_mul'_tmul_one_mem_span z

end Counit

/-! ### Points of a quotient by an ideal that is not a Hopf ideal -/

section QuotientPoints

/-- Reduction modulo `2`, as an algebra map over `ℤ`. -/
private def reduceModTwo : ZMod 4 →ₐ[ℤ] ZMod 2 :=
  (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toIntAlgHom

private theorem reduceModTwo_vanishes :
    ∀ x ∈ Ideal.span {(2 : ZMod 4)}, reduceModTwo x = 0 := by
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [map_mul, map_ofNat]
  exact mul_eq_zero_of_right _ (by decide)

/-- No Hopf structure is involved: `ZMod 4` is only a `ℤ`-algebra and `(2)` is an arbitrary ideal.
The algebra map out of `ZMod 4 ⧸ (2)` corresponding to reduction modulo `2` sends the class of `3`
to `1`. -/
example :
    (quotientPointsEquiv (R := ℤ) (A := ZMod 2) (Ideal.span {(2 : ZMod 4)})).symm
      ⟨reduceModTwo, reduceModTwo_vanishes⟩ (Ideal.Quotient.mk _ 3) = 1 := by
  decide

end QuotientPoints

end HopfKerTest
