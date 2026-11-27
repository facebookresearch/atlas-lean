/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CrossingResolutionProper

/-! # Consumers for the resolution of the crossing `X * Y = t ^ e`

The ring-level examples evaluate the chart, overlap and torus rings at the point
`(X, Y) = (2, 3)` of the crossing `X * Y = 6` over `ℚ`, so a wrong exponent or a swapped
coordinate in a twist, chart or transition map changes the values they check. The scheme-level
examples check the chart inclusions, the gluing pattern, the morphism to the crossing, and the
boundary cases `e = 0` (the resolution is empty) and `e = 1` (the resolution morphism is an
isomorphism). -/

noncomputable section

namespace CrossingResolutionProperTest

open AlgebraicGeometry CategoryTheory MvPolynomial MvPolynomial.CrossingQuotient

universe u

/-- The exact source statement, with the original binders. -/
public theorem exactSource {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    IsProper (Resolution.toCrossing t e) :=
  Resolution.isProper_toCrossing t e

/-- The statement applies over a base ring in a higher universe. -/
public example {W : Type (u + 1)} [CommRing W] (t : W) (e : ℕ) :
    IsProper (Resolution.toCrossing t e) :=
  Resolution.isProper_toCrossing t e

/-! ### Evaluation at the point `(X, Y) = (2, 3)` of `X * Y = 6` over `ℚ` -/

/-- The point `(X, Y) = (2, 3)` of the crossing `X * Y = 6`. -/
private abbrev pt : CrossingQuotient ℚ (6 : ℚ) →+* ℚ :=
  (lift (6 : ℚ) (2 : ℚ) 3 (by norm_num)).toRingHom

private theorem pt_U : pt (U 6) = 2 := lift_U _ _ _ _

private theorem pt_V : pt (V 6) = 3 := lift_V _ _ _ _

private theorem pt_algebraMap (q : ℚ) : pt (algebraMap ℚ _ q) = q := AlgHom.commutes _ q

/-- The point on the overlap ring, the localization at `Y`. -/
private abbrev evalOverlap : OverlapRing (6 : ℚ) →+* ℚ :=
  Localization.awayLift pt (V 6) (by rw [pt_V]; norm_num)

/-- The point on the localization at `X`. -/
private abbrev evalAwayU : Localization.Away (U (6 : ℚ)) →+* ℚ :=
  Localization.awayLift pt (U 6) (by rw [pt_U]; norm_num)

private theorem evalOverlap_algebraMap (c : CrossingQuotient ℚ (6 : ℚ)) :
    evalOverlap (algebraMap _ _ c) = pt c :=
  IsLocalization.Away.lift_eq _ _ c

private theorem evalAwayU_algebraMap (c : CrossingQuotient ℚ (6 : ℚ)) :
    evalAwayU (algebraMap _ _ c) = pt c :=
  IsLocalization.Away.lift_eq _ _ c

/-- The point on the torus ring, the localization at `X * Y`. -/
private abbrev evalTorus : TorusRing (6 : ℚ) →+* ℚ :=
  Localization.awayLift evalOverlap (algebraMap _ _ (U 6))
    (by rw [evalOverlap_algebraMap, pt_U]; norm_num)

private theorem evalTorus_algebraMap (c : OverlapRing (6 : ℚ)) :
    evalTorus (algebraMap _ _ c) = evalOverlap c :=
  IsLocalization.Away.lift_eq _ _ c

/-- A ring map to `ℚ` sends an inverse to the inverse of the image. -/
private theorem map_eq_inv {A : Type*} [CommRing A] (f : A →+* ℚ) {a b : A} (h : a * b = 1) :
    f b = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← map_mul, h, map_one])

private theorem evalOverlap_invSelf :
    evalOverlap (IsLocalization.Away.invSelf (V (6 : ℚ))) = 3⁻¹ := by
  rw [map_eq_inv evalOverlap (IsLocalization.Away.mul_invSelf (V (6 : ℚ))),
    evalOverlap_algebraMap, pt_V]

private theorem evalTorus_xT : evalTorus (xT 6) = 2 := by
  change evalTorus (algebraMap (CrossingQuotient ℚ (6 : ℚ)) (TorusRing (6 : ℚ)) (U 6)) = 2
  rw [IsScalarTower.algebraMap_apply (CrossingQuotient ℚ (6 : ℚ)) (OverlapRing (6 : ℚ))
      (TorusRing (6 : ℚ)) (U 6), evalTorus_algebraMap, evalOverlap_algebraMap, pt_U]

private theorem evalTorus_yT : evalTorus (yT 6) = 3 := by
  change evalTorus (algebraMap (CrossingQuotient ℚ (6 : ℚ)) (TorusRing (6 : ℚ)) (V 6)) = 3
  rw [IsScalarTower.algebraMap_apply (CrossingQuotient ℚ (6 : ℚ)) (OverlapRing (6 : ℚ))
      (TorusRing (6 : ℚ)) (V 6), evalTorus_algebraMap, evalOverlap_algebraMap, pt_V]

/-- `tT` is the product of the coordinates: `2 * 3 = 6`. -/
private theorem evalTorus_tT : evalTorus (tT 6) = 6 := by
  rw [← xT_mul_yT, map_mul, evalTorus_xT, evalTorus_yT]
  norm_num

/-- `tinv` is the inverse of `t`. -/
private theorem evalTorus_tinv : evalTorus (tinv 6) = 6⁻¹ := by
  rw [map_eq_inv evalTorus (tT_mul_tinv (6 : ℚ)), evalTorus_tT]

/-! ### Twists and charts in the torus ring -/

/-- The twist `i = 1` rescales `X` by `t⁻¹` and `Y` by `t`: `2 ↦ 2 / 6` and `3 ↦ 3 * 6`. -/
example : evalTorus (twistEquiv 6 1 (xT 6)) = 1 / 3 := by
  rw [twistEquiv_xT, map_mul, map_pow, evalTorus_xT, evalTorus_tinv]
  norm_num

example : evalTorus (twistEquiv 6 1 (yT 6)) = 18 := by
  rw [twistEquiv_yT, map_mul, map_pow, evalTorus_yT, evalTorus_tT]
  norm_num

/-- Its inverse rescales the other way: `2 ↦ 2 * 6` and `3 ↦ 3 / 6`. -/
example : evalTorus ((twistEquiv 6 1).symm (xT 6)) = 12 := by
  change evalTorus (twist 6 (tT 6 ^ 1) (tinv 6 ^ 1) (tT_pow_mul_tinv_pow 6 1) (xT 6)) = 12
  rw [twist_xT, map_mul, map_pow, evalTorus_xT, evalTorus_tT]
  norm_num

example : evalTorus ((twistEquiv 6 1).symm (yT 6)) = 1 / 2 := by
  change evalTorus (twist 6 (tT 6 ^ 1) (tinv 6 ^ 1) (tT_pow_mul_tinv_pow 6 1) (yT 6)) = 1 / 2
  rw [twist_yT, map_mul, map_pow, evalTorus_yT, evalTorus_tinv]
  norm_num

/-- The chart `i = 2` sits in the torus by `X ↦ X * t⁻²` and `Y ↦ Y * t²`. -/
example : evalTorus (torusChart 6 2 (U 6)) = 1 / 18 := by
  rw [torusChart_U, map_mul, map_pow, evalTorus_xT, evalTorus_tinv]
  norm_num

example : evalTorus (torusChart 6 2 (V 6)) = 108 := by
  rw [torusChart_V, map_mul, map_pow, evalTorus_yT, evalTorus_tT]
  norm_num

/-- The chart `i = 0` is the localization map itself. -/
example : evalTorus (torusChart 6 0 (U 6)) = 2 := by
  rw [torusChart_U, pow_zero, mul_one, evalTorus_xT]

/-- The overlap `i = 1` sits in the torus by the same rescaling as the chart `i = 1`: on `Y`,
`3 ↦ 3 * 6`, and on `Y⁻¹`, `3⁻¹ ↦ (3 * 6)⁻¹`. -/
example : evalTorus (torusOverlap 6 1 (algebraMap _ _ (V (6 : ℚ)))) = 18 := by
  rw [torusOverlap_algebraMap, torusChart_V, map_mul, map_pow, evalTorus_yT, evalTorus_tT]
  norm_num

private theorem evalTorus_torusOverlap_invSelf :
    evalTorus (torusOverlap 6 1 (IsLocalization.Away.invSelf (V (6 : ℚ)))) = 1 / 18 := by
  have h : torusOverlap 6 1 (algebraMap _ (OverlapRing (6 : ℚ)) (V (6 : ℚ))) *
      torusOverlap 6 1 (IsLocalization.Away.invSelf (V (6 : ℚ))) = 1 := by
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  rw [map_eq_inv evalTorus h, torusOverlap_algebraMap, torusChart_V, map_mul, map_pow,
    evalTorus_yT, evalTorus_tT]
  norm_num

/-- Going up to the next chart and then into the torus by the overlap `i = 1` gives the chart
`i = 2`: computed directly, `X ↦ Y⁻¹ ↦ 1 / 18`, the value of `torusChart 6 2` above. -/
example : evalTorus (torusOverlap 6 1 (transitionUp 6 (U 6))) = 1 / 18 := by
  rw [transitionUp_U, evalTorus_torusOverlap_invSelf]

example : (torusOverlap (6 : ℚ) 1).comp (transitionUp 6) = torusChart 6 2 :=
  torusOverlap_comp_transitionUp 6 1

/-- The twist `i = 0` is the identity. -/
example {W : Type u} [CommRing W] (t : W) (x : TorusRing t) : twistEquiv t 0 x = x := by
  have h : (twistEquiv t 0 : TorusRing t →ₐ[W] TorusRing t) = AlgHom.id W _ := by
    apply algHom_ext_torus
    · rw [AlgEquiv.coe_toAlgHom, twistEquiv_xT, pow_zero, mul_one, AlgHom.id_apply]
    · rw [AlgEquiv.coe_toAlgHom, twistEquiv_yT, pow_zero, mul_one, AlgHom.id_apply]
  exact congrArg (fun f : TorusRing t →ₐ[W] TorusRing t => f x) h

/-! ### The transition equivalence between the localizations at `X` and at `Y` -/

private theorem evalOverlap_transitionEquiv_U :
    evalOverlap (transitionEquiv 6 (algebraMap _ _ (U (6 : ℚ)))) = 3⁻¹ := by
  change evalOverlap (transitionUpAway 6 (algebraMap _ _ (U (6 : ℚ)))) = 3⁻¹
  rw [transitionUpAway_algebraMap, transitionUp_U, evalOverlap_invSelf]

/-- It sends `X` to `Y⁻¹` (above), `Y` to `t * Y` (`3 ↦ 18`), and `X⁻¹` to `Y` (`2⁻¹ ↦ 3`). -/
example : evalOverlap (transitionEquiv 6 (algebraMap _ _ (V (6 : ℚ)))) = 18 := by
  change evalOverlap (transitionUpAway 6 (algebraMap _ _ (V (6 : ℚ)))) = 18
  rw [transitionUpAway_algebraMap, transitionUp_V, map_mul, evalOverlap_algebraMap, pt_V,
    IsScalarTower.algebraMap_apply ℚ (CrossingQuotient ℚ (6 : ℚ)) (OverlapRing (6 : ℚ)),
    evalOverlap_algebraMap, pt_algebraMap]
  norm_num

example : evalOverlap (transitionEquiv 6 (IsLocalization.Away.invSelf (U (6 : ℚ)))) = 3 := by
  change (evalOverlap.comp (transitionEquiv (6 : ℚ)).toRingHom)
    (IsLocalization.Away.invSelf (U (6 : ℚ))) = 3
  rw [map_eq_inv _ (IsLocalization.Away.mul_invSelf (U (6 : ℚ)))]
  change (evalOverlap (transitionEquiv 6 (algebraMap _ _ (U (6 : ℚ)))))⁻¹ = 3
  rw [evalOverlap_transitionEquiv_U, inv_inv]

/-- Its inverse sends `Y` to `X⁻¹` (`3 ↦ 2⁻¹`) and `X` to `t * X` (`2 ↦ 12`). -/
example : evalAwayU ((transitionEquiv 6).symm (algebraMap _ _ (V (6 : ℚ)))) = 2⁻¹ := by
  change evalAwayU (transitionDownAway 6 (algebraMap _ _ (V (6 : ℚ)))) = 2⁻¹
  rw [transitionDownAway_algebraMap, transitionDown_V,
    map_eq_inv evalAwayU (IsLocalization.Away.mul_invSelf (U (6 : ℚ))), evalAwayU_algebraMap, pt_U]

example : evalAwayU ((transitionEquiv 6).symm (algebraMap _ _ (U (6 : ℚ)))) = 12 := by
  change evalAwayU (transitionDownAway 6 (algebraMap _ _ (U (6 : ℚ)))) = 12
  rw [transitionDownAway_algebraMap, transitionDown_U, map_mul, evalAwayU_algebraMap, pt_U,
    IsScalarTower.algebraMap_apply ℚ (CrossingQuotient ℚ (6 : ℚ)) (Localization.Away (U (6 : ℚ))),
    evalAwayU_algebraMap, pt_algebraMap]
  norm_num

/-! ### Chart inclusions -/

section schemes

variable {W : Type u} [CommRing W] (t : W)

example : IsOpenImmersion (overlapToChartLeft t) := inferInstance

example : IsOpenImmersion (overlapToChartRight t) := inferInstance

example (i : ℕ) : IsOpenImmersion (torusToChart t i) := inferInstance

example (i : ℕ) : IsOpenImmersion (torusToOverlap t i) := inferInstance

example (e : ℕ) (i : Fin e) : IsOpenImmersion (Resolution.ι t e i) := inferInstance

example (e : ℕ) (i : Fin e) (hi : (i : ℕ) + 1 < e) :
    IsOpenImmersion (Resolution.ιOverlap t e i hi) := inferInstance

example (e : ℕ) (h : 0 < e) : IsOpenImmersion (Resolution.ιTorus t e h) := inferInstance

example (e : ℕ) {a b : GlueIndex e} (f : a ⟶ b) : IsOpenImmersion ((glueDiagram t e).map f) :=
  inferInstance

example (e : ℕ) (i : (Resolution.openCover t e).I₀) : IsAffine ((Resolution.openCover t e).X i) :=
  inferInstance

/-- The charts are open subschemes covering the resolution. -/
example (e : ℕ) (x : Resolution t e) : ∃ i, x ∈ (Resolution.ι t e i).opensRange := by
  have hx : x ∈ (⊤ : (Resolution t e).Opens) := trivial
  rw [← Resolution.iSup_opensRange_ι t e] at hx
  exact TopologicalSpace.Opens.mem_iSup.mp hx

example (e : ℕ) (i : Fin e) : (Resolution.openCover t e).f i = Resolution.ι t e i := by simp

example : Nat.card (Resolution.openCover t 3).I₀ = 3 := by
  rw [Resolution.openCover_I₀, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ### The gluing pattern -/

/-- With three charts, the overlap `0` lies in charts `0` and `1` but not in chart `2`, distinct
charts are not comparable, and the torus lies in every piece. -/
example : (GlueIndex.overlap (0 : Fin 3) (by norm_num) : GlueIndex 3) ≤ GlueIndex.chart 0 := by
  simp

example : (GlueIndex.overlap (0 : Fin 3) (by norm_num) : GlueIndex 3) ≤ GlueIndex.chart 1 := by
  simp

example : ¬ (GlueIndex.overlap (0 : Fin 3) (by norm_num) : GlueIndex 3) ≤ GlueIndex.chart 2 := by
  simp

example : ¬ (GlueIndex.chart (0 : Fin 3) : GlueIndex 3) ≤ GlueIndex.chart 1 := by
  simp

example : (GlueIndex.torus (by norm_num) : GlueIndex 3) ≤ GlueIndex.overlap 1 (by norm_num) := by
  simp

example : ¬ (GlueIndex.chart (2 : Fin 3) : GlueIndex 3) ≤ GlueIndex.torus (by norm_num) := by
  simp

/-- The overlap `1` maps into chart `1` by the localization and into chart `2` by the
transition. -/
example (hi hle) : glueMap t 3 (.overlap 1 hi) (.chart 1) hle = overlapToChartLeft t := rfl

example (hi hle) : glueMap t 3 (.overlap 1 hi) (.chart 2) hle = overlapToChartRight t := rfl

/-- Adjacent charts agree on their overlap. -/
example (y : overlapScheme t) :
    Resolution.ι t 3 0 (overlapToChartLeft t y) = Resolution.ι t 3 1 (overlapToChartRight t y) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    Resolution.glue_condition t 3 0 (by norm_num)]
  rfl

/-- All charts agree on the torus. -/
example (i j : Fin 3) (z : torusScheme t) :
    Resolution.ι t 3 i (torusToChart t i z) = Resolution.ι t 3 j (torusToChart t j z) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Resolution.torusToChart_ι,
    Resolution.torusToChart_ι]

/-- Charts `0` and `2` of a three-chart resolution are not adjacent: a common point of both
lies in the torus. -/
example (x y : chartScheme t) (h : Resolution.ι t 3 0 x = Resolution.ι t 3 2 y) :
    x ∈ Set.range (torusToChart t 0) := by
  obtain ⟨a, ha0, ha2, z, hz, -⟩ := (Resolution.ι_apply_eq_iff t 3 x y).mp h
  cases a with
  | chart i =>
    rw [GlueIndex.chart_le_chart] at ha0 ha2
    exact absurd (ha0.symm.trans ha2) (by decide)
  | overlap i hi =>
    rw [GlueIndex.overlap_le_chart] at ha0 ha2
    rcases ha0 with h0 | h0 <;> rcases ha2 with h2 | h2 <;>
      simp only [Fin.ext_iff, Fin.val_zero, Fin.isValue] at h0 h2 <;> omega
  | torus h0 => exact ⟨z, hz⟩

/-- The overlap is the open set `Y ≠ 0` of the left chart and the open set `X ≠ 0` of the right
chart: on the node `X * Y = 0` over `ℚ`, the point `(X, Y) = (0, 1)` is not in the image of the
right map. -/
example : (⟨RingHom.ker (lift (0 : ℚ) (0 : ℚ) 1 (by norm_num)).toRingHom, RingHom.ker_isPrime _⟩ :
    chartScheme (0 : ℚ)) ∉ Set.range (overlapToChartRight (0 : ℚ)) := fun h =>
  U_notMem_of_mem_range_overlapToChartRight (0 : ℚ) h (by
    change (lift (0 : ℚ) (0 : ℚ) 1 _).toRingHom (U 0) = 0
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, lift_U])

/-- A point of the crossing `X * Y = 6` over `ℚ` with both coordinates nonzero lies in the torus
of every chart. -/
example (i : ℕ) : (⟨RingHom.ker pt, RingHom.ker_isPrime _⟩ : chartScheme (6 : ℚ)) ∈
    Set.range (torusToChart (6 : ℚ) i) := by
  refine mem_range_torusToChart (6 : ℚ) ?_ ?_ i
  · change pt (U 6) ≠ 0
    rw [pt_U]
    norm_num
  · change pt (V 6) ≠ 0
    rw [pt_V]
    norm_num

/-! ### The morphism to the crossing -/

/-- `toCrossing` is the only morphism restricting to the chart maps on every chart. -/
example (e : ℕ) (f : Resolution t e ⟶ crossingScheme (t ^ e))
    (hf : ∀ i, Resolution.ι t e i ≫ f =
      Spec.map (CommRingCat.ofHom (resolutionChart t e i).toRingHom)) :
    f = Resolution.toCrossing t e :=
  Resolution.hom_ext t e fun i => by rw [hf, Resolution.ι_toCrossing]

/-- Every chart lies over `Spec W` by its structure morphism. -/
example : Resolution.ι t 3 0 ≫ Resolution.toSpec t 3 = Resolution.ι t 3 2 ≫ Resolution.toSpec t 3 :=
  by rw [Resolution.ι_toSpec, Resolution.ι_toSpec]

/-- The torus maps to the crossing compatibly through every chart. -/
example : Resolution.ιTorus t 3 (by norm_num) ≫ Resolution.toCrossing t 3 =
    torusToChart t ((2 : Fin 3) : ℕ) ≫ Resolution.chartToCrossing t 3 2 := by
  rw [Resolution.ιTorus_toCrossing, Resolution.torusToChart_chartToCrossing]

end schemes

/-- Concretely, the torus point `(2, 3)` maps to the same point `(2, 108)` of `X * Y = 6 ^ 3`
through the charts `0`, `1` and `2`, computed directly in each chart. -/
example : evalTorus (torusChart 6 2 (resolutionChart 6 3 2 (U ((6 : ℚ) ^ 3)))) = 2 := by
  rw [resolutionChart_U, map_mul, AlgHom.commutes, torusChart_U]
  simp only [map_mul, map_pow, map_ofNat, evalTorus_xT, evalTorus_tinv]
  norm_num

example : evalTorus (torusChart 6 0 (resolutionChart 6 3 0 (V ((6 : ℚ) ^ 3)))) = 108 := by
  rw [resolutionChart_V, map_mul, AlgHom.commutes, torusChart_V]
  simp only [map_mul, map_pow, map_ofNat, evalTorus_yT]
  norm_num

example : evalTorus (torusChart 6 1 (resolutionChart 6 3 1 (V ((6 : ℚ) ^ 3)))) = 108 := by
  rw [resolutionChart_V, map_mul, AlgHom.commutes, torusChart_V]
  simp only [map_mul, map_pow, map_ofNat, evalTorus_yT]
  norm_num

example (i : Fin 3) : evalTorus (torusChart 6 i (resolutionChart 6 3 i (U ((6 : ℚ) ^ 3)))) = 2 := by
  rw [← AlgHom.comp_apply, Resolution.torusChart_comp_resolutionChart, AlgHom.comp_apply,
    resolutionChart_U, map_mul, AlgHom.commutes, torusChart_U]
  simp only [map_mul, map_pow, map_ofNat, evalTorus_xT, evalTorus_tinv]
  norm_num

/-! ### Boundary cases -/

/-- With no charts (`e = 0`), the index category and the resolution are empty. -/
example : IsEmpty (GlueIndex 0) :=
  ⟨fun a => by
    cases a with
    | chart i => exact i.elim0
    | overlap i _ => exact i.elim0
    | torus h => exact absurd h (lt_irrefl 0)⟩

example {W : Type u} [CommRing W] (t : W) : IsEmpty (Resolution t 0) :=
  ⟨fun x => (Resolution.exists_ι_apply_eq t 0 x).elim fun i _ => i.elim0⟩

/-- So for `e = 0` the resolution morphism is proper but not surjective: the crossing
`X * Y = 1` over `ℤ` has points. -/
example : IsProper (Resolution.toCrossing (6 : ℤ) 0) := Resolution.isProper_toCrossing 6 0

example : ¬ Function.Surjective (Resolution.toCrossing (6 : ℤ) 0) := by
  intro h
  have : Nontrivial (CrossingQuotient ℤ ((6 : ℤ) ^ 0)) :=
    (lift ((6 : ℤ) ^ 0) (1 : ℤ) 1 (by norm_num)).toRingHom.domain_nontrivial
  obtain ⟨P⟩ : Nonempty (PrimeSpectrum (CrossingQuotient ℤ ((6 : ℤ) ^ 0))) := inferInstance
  obtain ⟨x, -⟩ := h P
  exact (Resolution.exists_ι_apply_eq (6 : ℤ) 0 x).elim fun i _ => i.elim0

/-- The inverse of the single chart map `X ↦ X`, `Y ↦ Y` (up to `t ^ 1 = t`). -/
private def chartOneInv {W : Type u} [CommRing W] (t : W) :
    CrossingQuotient W t →ₐ[W] CrossingQuotient W (t ^ 1) :=
  lift t (U (t ^ 1)) (V (t ^ 1)) (by rw [U_mul_V, pow_one])

/-- With one chart (`e = 1`), the resolution morphism is an isomorphism. -/
example {W : Type u} [CommRing W] (t : W) : IsIso (Resolution.toCrossing t 1) := by
  let e : CrossingQuotient W (t ^ 1) ≃ₐ[W] CrossingQuotient W t :=
    AlgEquiv.ofAlgHom (resolutionChart t 1 0) (chartOneInv t)
      (algHom_ext_chart (by simp [chartOneInv, resolutionChart_U])
        (by simp [chartOneInv, resolutionChart_V]))
      (algHom_ext_chart (by simp [chartOneInv, resolutionChart_U])
        (by simp [chartOneInv, resolutionChart_V]))
  have hchart : IsIso (Resolution.chartToCrossing t 1 0) :=
    inferInstanceAs (IsIso (Spec.map e.toRingEquiv.toCommRingCatIso.hom))
  have hι : IsIso (Resolution.ι t 1 0) := by
    rw [isIso_iff_isOpenImmersion_and_epi_base, TopCat.epi_iff_surjective]
    refine ⟨inferInstance, fun x => ?_⟩
    obtain ⟨i, y, hy⟩ := Resolution.exists_ι_apply_eq t 1 x
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact ⟨y, hy⟩
  have : IsIso (Resolution.ι t 1 0 ≫ Resolution.toCrossing t 1) := by
    rw [Resolution.ι_toCrossing]
    exact hchart
  exact IsIso.of_isIso_comp_left (Resolution.ι t 1 0) (Resolution.toCrossing t 1)

/-- With a single chart, the resolution of the crossing of `t` over itself is proper. -/
public example (t : ℤ) : IsProper (Resolution.toCrossing t 1) :=
  Resolution.isProper_toCrossing t 1

/-! ### Properness and its parts -/

/-- A point `(X, Y) = (4, 9)` of `X * Y = 6 ^ 2` over the field `ℚ` factors through a chart. -/
example : ∃ (i : Fin 2) (g' : CrossingQuotient ℤ 6 →+* ℚ),
    g'.comp (resolutionChart (6 : ℤ) 2 i).toRingHom =
      (lift ((6 : ℤ) ^ 2) (4 : ℚ) 9 (by norm_num)).toRingHom :=
  exists_comp_resolutionChart_eq_of_valuationRing 6 (by norm_num) _

/-- The existence part of the valuative criterion and quasi-compactness give universal
closedness. -/
example {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    UniversallyClosed (Resolution.toCrossing t e) := by
  have := (Resolution.locallyOfFiniteType_and_quasiCompact_toCrossing t e).2
  exact UniversallyClosed.of_valuativeCriterion _
    (Resolution.valuativeCriterion_existence_toCrossing t e)

example {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    LocallyOfFiniteType (Resolution.toCrossing t e) :=
  (Resolution.locallyOfFiniteType_and_quasiCompact_toCrossing t e).1

/-- The resolution is a separated scheme, and so is its morphism to the crossing. -/
example {W : Type u} [CommRing W] (t : W) (e : ℕ) : (Resolution t e).IsSeparated :=
  (Resolution.isSeparated t e).1

example {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    IsSeparated (Resolution.toCrossing t e) :=
  (Resolution.isSeparated t e).2

/-- Properness gives universal closedness, so the resolution morphism is a closed map. -/
public example {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    UniversallyClosed (Resolution.toCrossing t e) :=
  have := Resolution.isProper_toCrossing t e
  inferInstance

example {W : Type u} [CommRing W] (t : W) (e : ℕ) : IsClosedMap (Resolution.toCrossing t e) := by
  have := Resolution.isProper_toCrossing t e
  exact (Resolution.toCrossing t e).isClosedMap

end CrossingResolutionProperTest
