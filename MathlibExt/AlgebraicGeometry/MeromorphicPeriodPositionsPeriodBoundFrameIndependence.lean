/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MeromorphicPeriodPositionMaps
public import MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels
public import MathlibExt.AlgebraicGeometry.AnalyticProObjectSites

/-!
# Frame independence of closed period bounds

Closed representation-lattice bounds are invariant under changes of the original integral frames.

Source: Fargues--Scholze, arXiv:2102.13459v4, Sections III.3 and VI.1--VI.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MeromorphicPeriodPositions

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Opposite
open MathlibExt.AlgebraicGeometry
open LocalWittCoefficientFields RelativeFarguesFontaineRings MarkedUntiltingPeriodModels
open LocalCoefficientScalarFrames AnalyticTateAdicModels AffinoidPeriodRings
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicHeckeModels AffinoidTorsorAlgebraizationModels
open CompletedTorsorSourceFrames MeromorphicTorsorCompletion MeromorphicPeriodPositionMaps
open AlgebraicGroupPointRepresentations AnalyticProObjectSites
open MathlibExt.LinearAlgebra.LocalizedLattices
open MathlibExt.CategoryTheory.SheafTorsorGroupoids
open scoped TensorProduct

section Transport

set_option backward.isDefEq.respectTransparency false

private theorem standard_map_integral_le (R : Type) [CommRing R] (r : R) (n : ℕ)
    (g : Matrix (Fin n) (Fin n) R) :
    (standard R r n).map
      ((Matrix.mulVecLin (g.map (algebraMap R (FractionRing R r)))).restrictScalars R) ≤
        standard R r n := by
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  refine ⟨g.mulVec v, ?_⟩
  ext i
  simp [standardMap, Matrix.mulVec, dotProduct, map_sum, map_mul]
private theorem standard_map_integral_eq (R : Type) [CommRing R] (r : R) (n : ℕ)
    (g : GL (Fin n) R) :
    (standard R r n).map
      ((Matrix.mulVecLin ((g : Matrix (Fin n) (Fin n) R).map
        (algebraMap R (FractionRing R r)))).restrictScalars R) = standard R r n := by
  apply le_antisymm (standard_map_integral_le R r n g.val)
  intro v hv
  refine ⟨(g.inv.map (algebraMap R (FractionRing R r))).mulVec v,
    standard_map_integral_le R r n g.inv ⟨v, hv, rfl⟩, ?_⟩
  change (g.val.map _).mulVec ((g.inv.map _).mulVec v) = v
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, g.val_inv, Matrix.map_one, Matrix.one_mulVec] <;> simp

private theorem standard_image_mul_integral (R : Type) [CommRing R] (r : R) (n : ℕ)
    (a : Matrix (Fin n) (Fin n) (FractionRing R r)) (g : GL (Fin n) R) :
    (standard R r n).map
      ((Matrix.mulVecLin (a * g.val.map (algebraMap R (FractionRing R r)))).restrictScalars R) =
        (standard R r n).map ((Matrix.mulVecLin a).restrictScalars R) := by
  rw [Matrix.mulVecLin_mul, LinearMap.restrictScalars_comp, Submodule.map_comp,
    standard_map_integral_eq]
private def integralEquiv (R : Type) [CommRing R] (r : R) (n : ℕ) (g : GL (Fin n) R) :
    Ambient R r n ≃ₗ[FractionRing R r] Ambient R r n :=
  (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.map (algebraMap R _) g)).toLinearEquiv
private theorem integralEquiv_scale (R : Type) [CommRing R] (r : R) (n : ℕ)
    (g : GL (Fin n) R) (a : FractionRing R r) :
    (integralEquiv R r n g).toLinearMap.restrictScalars R ∘ₗ scale R r n a =
      scale R r n a ∘ₗ (integralEquiv R r n g).toLinearMap.restrictScalars R := by
  apply LinearMap.ext
  intro v
  apply funext
  intro i
  change (integralEquiv R r n g (a • v)) i = (a • integralEquiv R r n g v) i
  rw [map_smul]
private theorem integralEquiv_lower (R : Type) [CommRing R] (r : R) (n : ℕ)
    (g : GL (Fin n) R) (N : ℕ) :
    (lower R r n N).map ((integralEquiv R r n g).toLinearMap.restrictScalars R) =
      lower R r n N := by
  change ((standard R r n).map (scale R r n (algebraMap R _ r ^ N))).map _ = _
  rw [← Submodule.map_comp, integralEquiv_scale, Submodule.map_comp]
  change ((standard R r n).map
    ((Matrix.mulVecLin (g.val.map (algebraMap R (FractionRing R r)))).restrictScalars R)).map _ = _
  rw [standard_map_integral_eq]
  rfl
private theorem integralEquiv_upper (R : Type) [CommRing R] (r : R) (n : ℕ)
    (g : GL (Fin n) R) (N : ℕ) :
    (upper R r n N).map ((integralEquiv R r n g).toLinearMap.restrictScalars R) =
      upper R r n N := by
  change ((standard R r n).map (scale R r n (IsLocalization.Away.invSelf r ^ N))).map _ = _
  rw [← Submodule.map_comp, integralEquiv_scale, Submodule.map_comp]
  change ((standard R r n).map
    ((Matrix.mulVecLin (g.val.map (algebraMap R (FractionRing R r)))).restrictScalars R)).map _ = _
  rw [standard_map_integral_eq]
  rfl
private noncomputable def latticeMap (R : Type) [CommRing R] (r : R) (n : ℕ)
    (g : GL (Fin n) R) (L : Lattice R r n) : Lattice R r n := by
  let e := integralEquiv R r n g
  let f := e.toLinearMap.restrictScalars R
  let q := Submodule.equivMapOfInjective f e.injective L.module
  refine { module := L.module.map f
           finite := Module.Finite.of_surjective q.toLinearMap q.surjective
           projective := Module.Projective.of_equiv' q
           rank := ?_
           full := ?_
           bounded := ?_ }
  · intro x
    let A := Localization.AtPrime x.asIdeal
    let eq := q.baseChange R A
    have h := L.rank x
    let := h.1
    exact ⟨Module.Free.of_equiv eq, eq.finrank_eq.symm.trans h.2⟩
  · have commutes : (localizationMap R r n (L.module.map f)).comp
        (q.baseChange R (FractionRing R r)).toLinearMap =
          e.toLinearMap.comp (localizationMap R r n L.module) := by
      ext a v
      simp [localizationMap, q, f]
    have hb := e.bijective.comp L.full
    change Function.Bijective (e.toLinearMap.comp (localizationMap R r n L.module)) at hb
    rw [← commutes] at hb
    exact (Function.Bijective.of_comp_iff _ (q.baseChange R (FractionRing R r)).bijective).mp hb
  · obtain ⟨N, hl, hu⟩ := L.bounded
    refine ⟨N, ?_, ?_⟩
    · exact (integralEquiv_lower R r n g N) ▸ Submodule.map_mono hl
    · exact (integralEquiv_upper R r n g N) ▸ Submodule.map_mono hu

private theorem det_integral_mul_mem (R : Type) [CommRing R] (S : Type) [CommRing S]
    [Algebra R S] (n k : ℕ) (a : Matrix (Fin k) (Fin n) R)
    (b : Matrix (Fin n) (Fin k) S) (I : Submodule R S)
    (h : ∀ rows : Fin k → Fin n, Function.Injective rows → (b.submatrix rows id).det ∈ I) :
    ((a.map (algebraMap R S)) * b).det ∈ I := by
  classical
  have hm : a.map (algebraMap R S) * b =
      fun i ↦ ∑ j, algebraMap R S (a i j) • b j := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def]
  rw [hm]
  change Matrix.detRowAlternating.toMultilinearMap
    (fun i ↦ ∑ j, algebraMap R S (a i j) • b j) ∈ I
  rw [MultilinearMap.map_sum]
  apply Submodule.sum_mem
  intro f _
  rw [MultilinearMap.map_smul_univ]
  simp only [RingHom.id_apply]
  rw [← map_prod (algebraMap R S)]
  change algebraMap R S (∏ i, a i (f i)) * (b.submatrix f id).det ∈ I
  rw [← Algebra.smul_def]
  by_cases hf : Function.Injective f
  · exact I.smul_mem _ (h f hf)
  · have hz : (b.submatrix f id).det = 0 :=
      Matrix.detRowAlternating.map_eq_zero_of_not_injective _
        (fun hinj ↦ hf (fun _ _ he ↦ hinj (congrArg b he)))
    rw [hz, smul_zero]
    exact I.zero_mem
private theorem coordinates_integral (R : Type) [CommRing R] (r : R) (n : ℕ)
    (L : Lattice R r n) (b : Module.Basis (Fin n) R L.module) (v : L.module) :
    PeriodLatticePluckerBounds.coordinates R r n L b v.val =
      fun i ↦ algebraMap R (FractionRing R r) (b.repr v i) := by
  let e := LinearEquiv.ofBijective (localizationMap R r n L.module) L.full
  have hv : e.symm v.val = (1 : FractionRing R r) ⊗ₜ[R] v := by
    apply e.injective
    simp [e, localizationMap]
  change ((b.baseChange (FractionRing R r)).map e).equivFun v.val = _
  rw [Module.Basis.map_equivFun]
  change (b.baseChange (FractionRing R r)).equivFun (e.symm v.val) = _
  rw [hv]
  ext i
  simp [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul, Algebra.smul_def]
private noncomputable def baseRestriction (R : Type) [CommRing R] (r : R) (n : ℕ)
    (L : Lattice R r n) (g : GL (Fin n) R) (hL : L.module = standard R r n) :
    L.module ≃ₗ[R] L.module :=
  ((integralEquiv R r n g).restrictScalars R).submoduleMap L.module |>.trans
    (LinearEquiv.ofEq _ _ (by rw [hL]; exact standard_map_integral_eq R r n g))
private noncomputable def coordinateMatrix (R : Type) [CommRing R] (r : R) (n : ℕ)
    (L : Lattice R r n) (b : Module.Basis (Fin n) R L.module)
    (g : GL (Fin n) R) (hL : L.module = standard R r n) : GL (Fin n) R :=
  Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (b.equivFun.symm.trans ((baseRestriction R r n L g hL).trans b.equivFun)))
private theorem coordinates_action_integral (R : Type) [CommRing R] (r : R) (n : ℕ)
    (L : Lattice R r n) (b : Module.Basis (Fin n) R L.module)
    (g : GL (Fin n) R) (hL : L.module = standard R r n) (v : L.module) :
    PeriodLatticePluckerBounds.coordinates R r n L b (integralEquiv R r n g v.val) =
      ((coordinateMatrix R r n L b g hL).val.map (algebraMap R (FractionRing R r))).mulVec
        (PeriodLatticePluckerBounds.coordinates R r n L b v.val) := by
  have he := Matrix.GeneralLinearGroup.toLin.apply_symm_apply
    (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (b.equivFun.symm.trans ((baseRestriction R r n L g hL).trans b.equivFun)))
  have hv := congrArg (fun e : LinearMap.GeneralLinearGroup R (Fin n → R) ↦
    e.val (b.equivFun v)) he
  change (coordinateMatrix R r n L b g hL).val.mulVec (b.equivFun v) =
    b.equivFun (baseRestriction R r n L g hL (b.equivFun.symm (b.equivFun v))) at hv
  rw [LinearEquiv.symm_apply_apply] at hv
  have hc := coordinates_integral R r n L b (baseRestriction R r n L g hL v)
  change PeriodLatticePluckerBounds.coordinates R r n L b (integralEquiv R r n g v.val) = _ at hc
  rw [hc, coordinates_integral]
  ext i
  change algebraMap R (FractionRing R r) (b.equivFun (baseRestriction R r n L g hL v) i) = _
  rw [← hv]
  simp [Module.Basis.equivFun_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
private theorem coordinates_action (R : Type) [CommRing R] (r : R) (n : ℕ)
    (L : Lattice R r n) (b : Module.Basis (Fin n) R L.module)
    (g : GL (Fin n) R) (hL : L.module = standard R r n) (v : Ambient R r n) :
    PeriodLatticePluckerBounds.coordinates R r n L b (integralEquiv R r n g v) =
      ((coordinateMatrix R r n L b g hL).val.map (algebraMap R (FractionRing R r))).mulVec
        (PeriodLatticePluckerBounds.coordinates R r n L b v) := by
  let c := (PeriodLatticePluckerBounds.coordinates R r n L b).toLinearMap
  let a := Matrix.mulVecLin
    ((coordinateMatrix R r n L b g hL).val.map (algebraMap R (FractionRing R r)))
  have he : (c.comp (integralEquiv R r n g).toLinearMap).comp
      (localizationMap R r n L.module) = (a.comp c).comp
        (localizationMap R r n L.module) := by
    ext x i
    change c (integralEquiv R r n g ((localizationMap R r n L.module) (1 ⊗ₜ[R] x))) i =
      a (c ((localizationMap R r n L.module) (1 ⊗ₜ[R] x))) i
    simp only [localizationMap, LinearMap.liftBaseChange_tmul, one_smul]
    exact congrArg (fun v ↦ v i) (coordinates_action_integral R r n L b g hL x)
  obtain ⟨w, hw⟩ := L.full.surjective v
  have hh := congrArg (fun f : FractionRing R r ⊗[R] L.module →ₗ[FractionRing R r] Ambient R r n ↦
    f w) he
  change c ((integralEquiv R r n g).toLinearMap v) = a (c v)
  simpa only [LinearMap.comp_apply, hw] using hh
private noncomputable def latticeEquiv (R : Type) [CommRing R] (r : R) (n : ℕ)
    (g : GL (Fin n) R) (M : Lattice R r n) : M.module ≃ₗ[R] (latticeMap R r n g M).module :=
  Submodule.equivMapOfInjective ((integralEquiv R r n g).toLinearMap.restrictScalars R)
    (integralEquiv R r n g).injective M.module
private noncomputable def coordinateColumns (R : Type) [CommRing R] (r : R) (n : ℕ)
    (L M : Lattice R r n) (b : Module.Basis (Fin n) R L.module)
    (k : ℕ) (v : Fin k → M.module) : Matrix (Fin n) (Fin k) (FractionRing R r) :=
  fun i j ↦ PeriodLatticePluckerBounds.coordinates R r n L b (v j).val i
private theorem minor_latticeMap (R : Type) [CommRing R] (r : R) (n : ℕ)
    (L M : Lattice R r n) (b : Module.Basis (Fin n) R L.module)
    (g : GL (Fin n) R) (hL : L.module = standard R r n) (k : ℕ)
    (rows : Fin k → Fin n) (v : Fin k → M.module) :
    PeriodLatticePluckerBounds.minor R r n L (latticeMap R r n g M) b k rows
      (fun j ↦ latticeEquiv R r n g M (v j)) =
      ((((coordinateMatrix R r n L b g hL).val.submatrix rows id).map
        (algebraMap R (FractionRing R r))) * coordinateColumns R r n L M b k v).det := by
  unfold PeriodLatticePluckerBounds.minor
  congr 1
  ext i j
  change PeriodLatticePluckerBounds.coordinates R r n L b
    (integralEquiv R r n g (v j).val) (rows i) = _
  rw [coordinates_action R r n L b g hL]
  rfl
private theorem determinantModule_latticeMap (R : Type) [CommRing R] (r : R) (n : ℕ)
    (L M : Lattice R r n) (b : Module.Basis (Fin n) R L.module)
    (g : GL (Fin n) R) (hL : L.module = standard R r n) :
    PeriodLatticePluckerBounds.determinantModule R r n L (latticeMap R r n g M) b =
      PeriodLatticePluckerBounds.determinantModule R r n L M b := by
  let q := latticeEquiv R r n g M
  let c := coordinateMatrix R r n L b g hL
  have hm (v : Fin n → M.module) :
      PeriodLatticePluckerBounds.minor R r n L (latticeMap R r n g M) b n id
        (fun j ↦ q (v j)) =
        c.val.det • PeriodLatticePluckerBounds.minor R r n L M b n id v := by
    rw [minor_latticeMap R r n L M b g hL]
    change (c.val.map (algebraMap R (FractionRing R r)) * _).det = _
    rw [Matrix.det_mul]
    have hd := (algebraMap R (FractionRing R r)).map_det c.val
    change algebraMap R (FractionRing R r) c.val.det = (c.val.map (algebraMap R _)).det at hd
    rw [← hd, Algebra.smul_def]
    rfl
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    have hv : v = fun j ↦ q (q.symm (v j)) := by
      funext j
      exact (q.apply_symm_apply (v j)).symm
    rw [hv, hm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun j ↦ q.symm (v j), rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    have hg := Submodule.smul_mem
      (PeriodLatticePluckerBounds.determinantModule R r n L (latticeMap R r n g M) b)
      c.inv.det (Submodule.subset_span ⟨fun j ↦ q (v j), rfl⟩)
    rw [hm, smul_smul, ← Matrix.det_mul, c.inv_val, Matrix.det_one, one_smul] at hg
    exact hg
private theorem pluckerBound_latticeMap (R : Type) [CommRing R] (r : R) (n : ℕ)
    (L M : Lattice R r n) (b : Module.Basis (Fin n) R L.module)
    (g : GL (Fin n) R) (hL : L.module = standard R r n) (weight : Fin n → ℤ)
    (hb : PeriodLatticePluckerBounds.IsBoundedBy R r n L M b weight) :
    PeriodLatticePluckerBounds.IsBoundedBy R r n L (latticeMap R r n g M) b weight := by
  refine ⟨hb.1, ?_, ?_⟩
  · intro k hk rows _ v
    let q := latticeEquiv R r n g M
    have hv : v = fun j ↦ q (q.symm (v j)) := by
      funext j
      exact (q.apply_symm_apply (v j)).symm
    rw [hv, minor_latticeMap R r n L M b g hL]
    apply det_integral_mul_mem
    intro rows' hi
    exact hb.2.1 k hk rows' hi (fun j ↦ q.symm (v j))
  · rw [determinantModule_latticeMap R r n L M b g hL]
    exact hb.2.2
private theorem positive_representationMatrix (p : ℕ) [Fact p.Prime] {E : MixedField p}
    (K : CoefficientData p E) {S : Base p K} (T : Untilting p K S)
    (s : ScalarLift p K S T) (x : Parameter p K T s)
    (G : Over (Spec (.of E.field))) [GrpObj G] (n : ℕ) (ρ : Representation E.field G n)
    (a : PeriodGroupPositionModels.PositiveGroup p K T s G) :
    PeriodGroupPositionModels.representationMatrix p K T s x G ρ
      (PeriodGroupPositionModels.positiveMap p K T s x G a) =
      Matrix.GeneralLinearGroup.map
        (algebraMap (DeRhamPlus p T.affine.pair)
          (FractionRing (DeRhamPlus p T.affine.pair) x.value))
          ((ρ.app (PeriodGroupPositionModels.positiveTest p K T s)).hom a) :=
  ConcreteCategory.congr_hom (ρ.naturality (PeriodGroupPositionModels.localizationTest p K T s x)) a
private theorem representedModule_mul (p : ℕ) [Fact p.Prime] {E : MixedField p}
    (K : CoefficientData p E) {S : Base p K} (T : Untilting p K S)
    (s : ScalarLift p K S T) (x : Parameter p K T s)
    (G : Over (Spec (.of E.field))) [GrpObj G] (n : ℕ) (ρ : Representation E.field G n)
    (g : PeriodGroupPositionModels.GenericGroup p K T s x G)
    (a b : PeriodGroupPositionModels.PositiveGroup p K T s G) :
    PeriodGroupPositionModels.representedModule p K T s x G ρ
      (PeriodGroupPositionModels.positiveMap p K T s x G a * g *
        PeriodGroupPositionModels.positiveMap p K T s x G b) =
      (PeriodGroupPositionModels.representedModule p K T s x G ρ g).map
        ((integralEquiv (DeRhamPlus p T.affine.pair) x.value n
          ((ρ.app
            (PeriodGroupPositionModels.positiveTest p K T s)).hom a)).toLinearMap.restrictScalars
              (DeRhamPlus p T.affine.pair)) := by
  let ga : GL (Fin n) (DeRhamPlus p T.affine.pair) :=
    (ρ.app (PeriodGroupPositionModels.positiveTest p K T s)).hom a
  let gb : GL (Fin n) (DeRhamPlus p T.affine.pair) :=
    (ρ.app (PeriodGroupPositionModels.positiveTest p K T s)).hom b
  have ha := positive_representationMatrix p K T s x G n ρ a
  have hb := positive_representationMatrix p K T s x G n ρ b
  have hm : PeriodGroupPositionModels.representationMatrix p K T s x G ρ
      (PeriodGroupPositionModels.positiveMap p K T s x G a * g *
        PeriodGroupPositionModels.positiveMap p K T s x G b) =
      PeriodGroupPositionModels.representationMatrix p K T s x G ρ
        (PeriodGroupPositionModels.positiveMap p K T s x G a) *
      PeriodGroupPositionModels.representationMatrix p K T s x G ρ g *
      PeriodGroupPositionModels.representationMatrix p K T s x G ρ
        (PeriodGroupPositionModels.positiveMap p K T s x G b) := by
    simp only [PeriodGroupPositionModels.representationMatrix, map_mul]
  unfold PeriodGroupPositionModels.representedModule
  rw [hm]
  rw [ha, hb]
  change (standard (DeRhamPlus p T.affine.pair) x.value n).map
    ((Matrix.mulVecLin
      (ga.val.map (algebraMap (DeRhamPlus p T.affine.pair)
        (FractionRing (DeRhamPlus p T.affine.pair) x.value)) *
        (PeriodGroupPositionModels.representationMatrix p K T s x G ρ g).val *
          gb.val.map (algebraMap (DeRhamPlus p T.affine.pair)
            (FractionRing (DeRhamPlus p T.affine.pair) x.value)))).restrictScalars _) = _
  rw [standard_image_mul_integral, Matrix.mulVecLin_mul, LinearMap.restrictScalars_comp,
    Submodule.map_comp]
  rfl
private theorem representationBounded_mul (p : ℕ) [Fact p.Prime] {E : MixedField p}
    (K : CoefficientData p E) {S : Base p K} (T : Untilting p K S)
    (s : ScalarLift p K S T) (x : Parameter p K T s)
    (G : Over (Spec (.of E.field))) [GrpObj G]
    (g : PeriodGroupPositionModels.GenericGroup p K T s x G)
    (a b : PeriodGroupPositionModels.PositiveGroup p K T s G) (μ : Cocharacter E.field G)
    (hg : PeriodGroupPositionModels.IsRepresentationBounded p K T s x G g μ) :
    PeriodGroupPositionModels.IsRepresentationBounded p K T s x G
      (PeriodGroupPositionModels.positiveMap p K T s x G a * g *
        PeriodGroupPositionModels.positiveMap p K T s x G b) μ := by
  intro n ρ W
  obtain ⟨F, B, hb⟩ := hg n ρ W
  let ga : GL (Fin n) (DeRhamPlus p T.affine.pair) :=
    (ρ.app (PeriodGroupPositionModels.positiveTest p K T s)).hom a
  let B' : PeriodGroupPositionModels.RepresentedLattice p K T s x G ρ
      (PeriodGroupPositionModels.positiveMap p K T s x G a * g *
        PeriodGroupPositionModels.positiveMap p K T s x G b) :=
    { lattice := latticeMap (DeRhamPlus p T.affine.pair) x.value n ga B.lattice
      normalized := by
        change B.lattice.module.map
          ((integralEquiv (DeRhamPlus p T.affine.pair) x.value n ga).toLinearMap.restrictScalars
            (DeRhamPlus p T.affine.pair)) = _
        rw [representedModule_mul p K T s x G n ρ g a b, B.normalized] }
  exact ⟨F, B', pluckerBound_latticeMap (DeRhamPlus p T.affine.pair) x.value n
    F.lattice B.lattice F.basis ga F.normalized W.weight hb⟩

private def regularValue (E : Type) [CommRing E] (G : Over (Spec (.of E))) [GrpObj G]
    (X : Over (Spec (.of E)))
    (e : WittDiscTorsorModels.regularAction E G X ⟶ WittDiscTorsorModels.regularAction E G X)
    (T : WittDiscTorsorModels.Site E X) :
    (WittDiscTorsorModels.groupSheaf E G X).obj.obj (op T) →
      (WittDiscTorsorModels.groupSheaf E G X).obj.obj (op T) := e.val.hom.app (op T)
private theorem regular_value (E : Type) [CommRing E] (G : Over (Spec (.of E))) [GrpObj G]
    (X : Over (Spec (.of E)))
    (e : WittDiscTorsorModels.regularAction E G X ⟶ WittDiscTorsorModels.regularAction E G X)
    (T : WittDiscTorsorModels.Site E X)
    (x : (WittDiscTorsorModels.groupSheaf E G X).obj.obj (op T)) :
    regularValue E G X e T x = regularValue E G X e T 1 * x := by
  have h := e.property (op T)
    (1 : (WittDiscTorsorModels.groupSheaf E G X).obj.obj (op T)) x
  change regularValue E G X e T (1 * x) = regularValue E G X e T 1 * x at h
  simpa only [one_mul] using h
private noncomputable def regularPoint (E : Type) [CommRing E] (G : Over (Spec (.of E))) [GrpObj G]
    (X : Over (Spec (.of E)))
    (e : WittDiscTorsorModels.regularAction E G X ⟶ WittDiscTorsorModels.regularAction E G X) :
    (WittDiscTorsorModels.baseGroupPresheaf E G).obj (op X) :=
  regularValue E G X e (Over.mk (𝟙 X)) 1
private theorem regularPoint_comp (E : Type) [CommRing E]
    (G : Over (Spec (.of E))) [GrpObj G] (X : Over (Spec (.of E)))
    (e h : WittDiscTorsorModels.regularAction E G X ⟶ WittDiscTorsorModels.regularAction E G X) :
    regularPoint E G X (e ≫ h) = regularPoint E G X h * regularPoint E G X e := by
  change regularValue E G X h (Over.mk (𝟙 X)) (regularValue E G X e (Over.mk (𝟙 X)) 1) = _
  rw [regular_value]
  rfl
private theorem regular_restrict_value (E : Type) [CommRing E]
    (G : Over (Spec (.of E))) [GrpObj G] {X Y : Over (Spec (.of E))} (f : Y ⟶ X)
    (e : WittDiscTorsorModels.regularAction E G X ⟶ WittDiscTorsorModels.regularAction E G X) :
    regularPoint E G Y ((WittDiscTorsorModels.actionPullback G f).map e) =
      ((WittDiscTorsorModels.baseGroupPresheaf E G).map f.op).hom
        (regularPoint E G X e) := by
  let S := (Over.map f).obj (Over.mk (𝟙 Y))
  let u : S ⟶ Over.mk (𝟙 X) := Over.homMk S.hom (by simp)
  have hn := congrArg
    (fun e ↦ e (1 : (WittDiscTorsorModels.groupSheaf E G X).obj.obj (op (Over.mk (𝟙 X)))))
    (e.val.hom.naturality u.op)
  simp only [WittDiscTorsorModels.groupSheaf, WittDiscTorsorModels.regularAction, groupSets,
    sheafCompose_obj_obj, Functor.comp_obj, Over.map_obj_hom, Over.mk_left, Over.mk_hom,
    Category.id_comp, Functor.comp_map, Functor.sheafPushforwardContinuous_obj_obj_map,
    Over.forget_obj, Over.map_obj_left, Quiver.Hom.unop_op, Over.forget_map, Over.homMk_left,
    TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, comp_apply, map_one, S, u] at hn
  change regularValue E G X e S 1 = _
  change regularValue E G X e S 1 =
    ((WittDiscTorsorModels.baseGroupPresheaf E G).map f.op).hom
      (regularValue E G X e (Over.mk (𝟙 X)) 1) at hn
  exact hn
private theorem regularPoint_change (E : Type) [CommRing E]
    (G : Over (Spec (.of E))) [GrpObj G] {X Y : Over (Spec (.of E))} (f : Y ⟶ X)
    (L R : Action (WittDiscTorsorModels.topology E X) (WittDiscTorsorModels.groupSheaf E G X))
    (left left' : L ≅ WittDiscTorsorModels.regularAction E G X)
    (right right' : R ≅ WittDiscTorsorModels.regularAction E G X)
    (c : (WittDiscTorsorModels.actionPullback G f).obj L ≅
      (WittDiscTorsorModels.actionPullback G f).obj R) :
    regularPoint E G Y
      (((WittDiscTorsorModels.actionPullback G f).mapIso left').symm ≪≫ c ≪≫
        (WittDiscTorsorModels.actionPullback G f).mapIso right').hom =
      ((WittDiscTorsorModels.baseGroupPresheaf E G).map f.op).hom
        (regularPoint E G X (right.symm ≪≫ right').hom) *
      regularPoint E G Y
        (((WittDiscTorsorModels.actionPullback G f).mapIso left).symm ≪≫ c ≪≫
          (WittDiscTorsorModels.actionPullback G f).mapIso right).hom *
      ((WittDiscTorsorModels.baseGroupPresheaf E G).map f.op).hom
        (regularPoint E G X (left'.symm ≪≫ left).hom) := by
  let F := WittDiscTorsorModels.actionPullback G f
  let a := right.symm ≪≫ right'
  let b := left'.symm ≪≫ left
  let old := (F.mapIso left).symm ≪≫ c ≪≫ F.mapIso right
  have he : ((F.mapIso left').symm ≪≫ c ≪≫ F.mapIso right').hom =
      (F.mapIso b).hom ≫ old.hom ≫ (F.mapIso a).hom := by
    simp [a, b, old, Category.assoc]
  change regularPoint E G Y ((F.mapIso left').symm ≪≫ c ≪≫ F.mapIso right').hom = _
  rw [he, regularPoint_comp, regularPoint_comp]
  change regularPoint E G Y ((WittDiscTorsorModels.actionPullback G f).map a.hom) *
    regularPoint E G Y old.hom *
    regularPoint E G Y ((WittDiscTorsorModels.actionPullback G f).map b.hom) = _
  rw [regular_restrict_value E G f a.hom, regular_restrict_value E G f b.hom]
private theorem framedElement_double_mul (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    (G : Over (Spec (.of E))) [GrpObj G]
    (H : ∀ W : ESpace p E, GroupDescent p E G W) (P : PullbackPreservation p E G H)
    {X Z : ESpace p E} (d : Z ⟶ X) (U : Puncture p E d) (Q : PoleChart p E d U)
    (Aq : Algebraization p E G H Q.space)
    (Bq : FpqcPreservesTorsors E G (completionBaseMap p E d U Q))
    (F : SourceFrames p E G H P d U Q Aq)
    (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter))
    (C : MeromorphicTorsorCompletion.CompletionComparison p E G H P d U Q Aq Bq F h)
    (M : Hecke p E G H P d U)
    (left left' : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).left)
    (right right' : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).right) :
    ∃ a b : (groups E G).obj (MeromorphicPeriodPositionMaps.positiveTest p E d U Q),
      framedElement p E G H P d U Q Aq Bq F h C M left' right' =
        ((groups E G).map (positiveTestMap p E d U Q)).hom a *
          framedElement p E G H P d U Q Aq Bq F h C M left right *
            ((groups E G).map (positiveTestMap p E d U Q)).hom b := by
  let NL := (originalModification p E G H P d U M).left
  let NR := (originalModification p E G H P d U M).right
  let l := formalFrame p E G H P d U Q Aq Bq (F NL left)
  let l' := formalFrame p E G H P d U Q Aq Bq (F NL left')
  let r := formalFrame p E G H P d U Q Aq Bq (F NR right)
  let r' := formalFrame p E G H P d U Q Aq Bq (F NR right')
  let a : (groups E G).obj (MeromorphicPeriodPositionMaps.positiveTest p E d U Q) :=
    (regularPoint E G (positiveScheme p E d U Q) (r.symm ≪≫ r').hom).down
  let b : (groups E G).obj (MeromorphicPeriodPositionMaps.positiveTest p E d U Q) :=
    (regularPoint E G (positiveScheme p E d U Q) (l'.symm ≪≫ l).hom).down
  refine ⟨a, b, ?_⟩
  have hh := regularPoint_change E G (localization p E d U Q) _ _ l l' r r' (C.comparison.app M)
  have hd := congrArg ULift.down hh
  change framedElement p E G H P d U Q Aq Bq F h C M left' right' =
    ((groups E G).map (positiveTestMap p E d U Q)).hom a *
      framedElement p E G H P d U Q Aq Bq F h C M left right *
        ((groups E G).map (positiveTestMap p E d U Q)).hom b at hd
  exact hd

private def positivePeriodTestMap (p : ℕ) [Fact p.Prime] {E : MixedField p}
    (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q) :
    MeromorphicPeriodPositionMaps.positiveTest p E.field d U Q ⟶
      PeriodGroupPositionModels.positiveTest p K V.chart.refinement.untilt V.scalar := by
  letI := (positiveScalars p E.field d U Q).toAlgebra
  letI := V.scalar.map.toAlgebra
  exact CommAlgCat.ofHom
    { __ := (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).toRingHom
      commutes' := B.scalars }
private theorem periodTest_square (p : ℕ) [Fact p.Prime] {E : MixedField p}
    (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q) :
    positiveTestMap p E.field d U Q ≫ periodTestMap p K R I A T D V d U Q B =
      positivePeriodTestMap p K R I A T D V d U Q B ≫
        PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt
          V.scalar V.parameter := by
  ext a
  change genericPeriodMap p K R I A T D V d U Q B
    (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q) a) = _
  exact genericPeriodMap_coefficients p K R I A T D V d U Q B a
private theorem period_positive_value (p : ℕ) [Fact p.Prime] {E : MixedField p}
    (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q)
    (G : Over (Spec (.of E.field))) [GrpObj G]
    (a : (groups E.field G).obj (MeromorphicPeriodPositionMaps.positiveTest p E.field d U Q)) :
    ((groups E.field G).map (periodTestMap p K R I A T D V d U Q B)).hom
      (((groups E.field G).map (positiveTestMap p E.field d U Q)).hom a) =
      PeriodGroupPositionModels.positiveMap p K V.chart.refinement.untilt V.scalar V.parameter G
        (((groups E.field G).map (positivePeriodTestMap p K R I A T D V d U Q B)).hom a) := by
  have hs := congrArg (fun f ↦ ((groups E.field G).map f).hom a)
    (periodTest_square p K R I A T D V d U Q B)
  rw [Functor.map_comp, Functor.map_comp] at hs
  exact hs

end Transport

/-- For a fixed completed comparison, replacing either integral frame preserves the
representation-lattice Plücker bound. -/
public theorem periodBound_frame_independence
    (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q)
    (G : Over (Spec (.of E.field))) [GrpObj G]
    (H : ∀ W : ESpace p E.field, GroupDescent p E.field G W)
    (P : PullbackPreservation p E.field G H)
    (Aq : Algebraization p E.field G H Q.space)
    (Bq : FpqcPreservesTorsors E.field G (completionBaseMap p E.field d U Q))
    (F : SourceFrames p E.field G H P d U Q Aq)
    (h : IsUnit (sectionMap p E.field Q.puncture.map Q.parameter))
    (C : MeromorphicTorsorCompletion.CompletionComparison p E.field G H P d U Q Aq Bq F h)
    (M : Hecke p E.field G H P d U)
    (left : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).left)
    (right : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).right)
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E.field)) G]
    (left' : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).left)
    (right' : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).right)
    (μ : Cocharacter E.field G) :
    IsPeriodBounded p K R I A T D V d U Q B G H P Aq Bq F h C M left right μ ↔
      IsPeriodBounded p K R I A T D V d U Q B G H P Aq Bq F h C M left' right' μ
    := by
  obtain ⟨a, b, hg⟩ := framedElement_double_mul p E.field G H P d U Q Aq Bq F h C M
    left left' right right'
  let a' : PeriodGroupPositionModels.PositiveGroup p K V.chart.refinement.untilt V.scalar G :=
    ((groups E.field G).map (positivePeriodTestMap p K R I A T D V d U Q B)).hom a
  let b' : PeriodGroupPositionModels.PositiveGroup p K V.chart.refinement.untilt V.scalar G :=
    ((groups E.field G).map (positivePeriodTestMap p K R I A T D V d U Q B)).hom b
  have he : periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left' right' =
      PeriodGroupPositionModels.positiveMap p K V.chart.refinement.untilt
        V.scalar V.parameter G a' *
        periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left right *
          PeriodGroupPositionModels.positiveMap p K V.chart.refinement.untilt
            V.scalar V.parameter G b' := by
    unfold periodElement
    rw [hg, map_mul, map_mul, period_positive_value p K R I A T D V d U Q B G a,
      period_positive_value p K R I A T D V d U Q B G b]
  unfold IsPeriodBounded
  rw [he]
  constructor
  · exact representationBounded_mul p K V.chart.refinement.untilt V.scalar V.parameter G
      (periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left right) a' b' μ
  · intro hb
    have hh := representationBounded_mul p K V.chart.refinement.untilt V.scalar V.parameter G
      (PeriodGroupPositionModels.positiveMap p K V.chart.refinement.untilt
        V.scalar V.parameter G a' *
        periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left right *
          PeriodGroupPositionModels.positiveMap p K V.chart.refinement.untilt
            V.scalar V.parameter G b')
      a'⁻¹ b'⁻¹ μ hb
    simpa only [map_inv, mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left] using hh

end WantedExt.AlgebraicGeometry.MeromorphicPeriodPositions
