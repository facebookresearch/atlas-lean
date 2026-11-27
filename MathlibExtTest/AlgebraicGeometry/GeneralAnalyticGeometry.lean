/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralAnalyticGeometry
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
Provider-free interface checks: genuine two-variable holomorphic evaluation,
and the relations of an ideal holding in its model through quotient,
sheafification and pullback, without a manifold or GAGA provider. For the double point
`(z²)`, the nilpotent `z` itself survives: it is nonzero on every neighbourhood of the origin
in `𝒪/(z²)`, its germ at the origin is nonzero before and after sheafification, and its image in
the global sections of the structure sheaf on the zero set is nonzero.
-/

open MathlibExt.AlgebraicGeometry.PolynomialAnalyticSpaces
open scoped Manifold ContDiff

@[expose] public noncomputable section

example : polynomialSections 2 ⊤
    ((MvPolynomial.X (0 : Fin 2)) ^ 2 + 3 * MvPolynomial.X 1 - MvPolynomial.C 7)
    ⟨![2, 5], by trivial⟩ = (12 : ℂ) := by
  rw [polynomialSections_eval]
  norm_num

/-- The relation `X² = 0` of the ideal `(X²)` defining the double point holds in
its model. -/
example : polynomialMap 1
    (Ideal.span {(MvPolynomial.X (0 : Fin 1)) ^ 2})
    (MvPolynomial.X (0 : Fin 1)) ^ 2 = 0 := by
  rw [← map_pow]
  exact polynomialMap_relation 1 _ _ (Ideal.subset_span (Set.mem_singleton _))

example : polynomialMap 1
    (Ideal.span {MvPolynomial.X (0 : Fin 1) - MvPolynomial.C 3})
    (MvPolynomial.X (0 : Fin 1)) =
      polynomialMap 1 (Ideal.span {MvPolynomial.X (0 : Fin 1) - MvPolynomial.C 3})
        (MvPolynomial.C 3) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact polynomialMap_relation 1 _ _ (Ideal.subset_span (Set.mem_singleton _))

namespace GeneralAnalyticGeometryTest.DoublePoint

open CategoryTheory Opposite TopologicalSpace Filter Topology

private abbrev doublePoint : Ideal (PolynomialRing 1) :=
  Ideal.span {(MvPolynomial.X (0 : Fin 1)) ^ 2}

/-- On every neighbourhood of the origin, the coordinate `z` is not a multiple of `z²` by a
continuous function: `z = z² g` would force `z g = 1` away from `0` and `z g = 0` at `0`. -/
private theorem coordinate_not_mem_analyticIdeal (U : Opens (Coordinates 1))
    (h0 : (0 : Coordinates 1) ∈ U) :
    polynomialSections 1 U (MvPolynomial.X 0) ∉ analyticIdeal 1 doublePoint U := by
  intro hmem
  rw [analyticIdeal, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hmem
  obtain ⟨g, hg⟩ := hmem
  -- pointwise: z = g * z²
  have hpt : ∀ p : U, p.1 0 = g p * (p.1 0) ^ 2 := by
    intro p
    have := congrArg (fun F : HolomorphicFunctions 1 U => F p) hg
    have e1 : (polynomialSections 1 U (MvPolynomial.X 0)) p = p.1 0 := by
      rw [polynomialSections_eval]; simp
    have e2 : (polynomialSections 1 U ((MvPolynomial.X 0) ^ 2)) p = (p.1 0) ^ 2 := by
      rw [polynomialSections_eval]; simp
    have hmul : (g * polynomialSections 1 U ((MvPolynomial.X 0) ^ 2)) p =
        g p * (polynomialSections 1 U ((MvPolynomial.X 0) ^ 2)) p := rfl
    rw [hmul, e1, e2] at this
    exact this.symm
  let φ : U → ℂ := fun p => p.1 0 * g p
  have hgc : Continuous (fun p : U => g p) := g.prop.continuous
  have hφc : Continuous φ :=
    ((continuous_apply 0).comp continuous_subtype_val).mul hgc
  let x : U := ⟨0, h0⟩
  have hφx : φ x = 0 := by simp [φ, x]
  have hφne : ∀ p : U, p.1 ≠ 0 → φ p = 1 := by
    intro p hp
    have hp0 : p.1 0 ≠ 0 := by
      intro h; apply hp; funext i; fin_cases i; simpa using h
    have := hpt p
    have : p.1 0 * (1 - g p * p.1 0) = 0 := by rw [mul_sub, mul_one]; linear_combination this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hp0
    · simp only [φ]; linear_combination -h
  -- punctured neighbourhoods of `x` inside `U`
  let F : Filter U := Filter.comap Subtype.val (𝓝[≠] (0 : Coordinates 1))
  have hFx : F ≤ 𝓝 x := by
    rw [nhds_subtype]
    exact Filter.comap_mono nhdsWithin_le_nhds
  have hFne : F.NeBot := by
    apply Filter.comap_neBot
    intro t ht
    have hU : (U : Set (Coordinates 1)) ∈ 𝓝[≠] (0 : Coordinates 1) :=
      nhdsWithin_le_nhds (U.isOpen.mem_nhds h0)
    obtain ⟨y, hyt, hyU⟩ :=
      Filter.nonempty_of_mem (f := 𝓝[≠] (0 : Coordinates 1)) (Filter.inter_mem ht hU)
    exact ⟨⟨y, hyU⟩, hyt⟩
  have h1 : Tendsto φ F (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    have : {p : U | p.1 ≠ 0} ∈ F := ⟨{0}ᶜ, self_mem_nhdsWithin, fun p hp => hp⟩
    filter_upwards [this] with p hp
    exact (hφne p hp).symm
  have h2 : Tendsto φ F (𝓝 0) := by
    rw [← hφx]; exact (hφc.tendsto x).mono_left hFx
  exact one_ne_zero (tendsto_nhds_unique h1 h2)

/-- The class of `z` restricts to the class of `z`. -/
private theorem quotient_map_coordinate {U V : Opens (Coordinates 1)} (f : op U ⟶ op V) :
    (quotientPresheaf 1 doublePoint).map f
        (Ideal.Quotient.mk (analyticIdeal 1 doublePoint U)
          (polynomialSections 1 U (MvPolynomial.X 0))) =
      Ideal.Quotient.mk (analyticIdeal 1 doublePoint V)
        (polynomialSections 1 V (MvPolynomial.X 0)) := by
  show Ideal.Quotient.mk (analyticIdeal 1 doublePoint V)
      (((ambientPresheaf 1).map f).hom (polynomialSections 1 U (MvPolynomial.X 0))) = _
  exact congrArg (Ideal.Quotient.mk _)
    (RingHom.congr_fun (polynomialSections_naturality 1 f) (MvPolynomial.X 0))

/-- In the stalk at the origin of the quotient presheaf `𝒪/(z²)`, the germ of `z` is nonzero. -/
private theorem presheaf_germ_coordinate_ne_zero :
    TopCat.Presheaf.germ (X := TopCat.of (Coordinates 1)) (quotientPresheaf 1 doublePoint) ⊤ 0
        trivial (Ideal.Quotient.mk (analyticIdeal 1 doublePoint ⊤)
          (polynomialSections 1 ⊤ (MvPolynomial.X 0))) ≠ 0 := by
  intro h
  have h' := h.trans (map_zero (ConcreteCategory.hom (TopCat.Presheaf.germ
    (X := TopCat.of (Coordinates 1)) (quotientPresheaf 1 doublePoint) ⊤ 0 trivial))).symm
  obtain ⟨W, hW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq (X := TopCat.of (Coordinates 1))
    (quotientPresheaf 1 doublePoint) 0 trivial trivial _ _ h'
  rw [quotient_map_coordinate, map_zero] at e
  exact coordinate_not_mem_analyticIdeal W hW (Ideal.Quotient.eq_zero_iff_mem.mp e)

/-- The nilpotent `z` survives sheafification: in the stalk at the origin of the sheaf
`𝒪/(z²)` (the double point on the ambient line), the germ of `z` is nonzero. -/
private theorem sheaf_germ_coordinate_ne_zero :
    TopCat.Presheaf.germ (quotientSheaf 1 doublePoint).obj ⊤ 0 trivial
        ((toSheafify (Opens.grothendieckTopology (Coordinates 1))
          (quotientPresheaf 1 doublePoint)).app (op ⊤)
            (Ideal.Quotient.mk (analyticIdeal 1 doublePoint ⊤)
              (polynomialSections 1 ⊤ (MvPolynomial.X 0)))) ≠ 0 := by
  have : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat (0 : TopCat.of (Coordinates 1))).map
      (toSheafify (Opens.grothendieckTopology (Coordinates 1)) (quotientPresheaf 1 doublePoint))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (0 : TopCat.of (Coordinates 1))
      CommRingCat (quotientPresheaf 1 doublePoint)
  intro h
  have key := TopCat.Presheaf.stalkFunctor_map_germ_apply (C := CommRingCat)
    (X := TopCat.of (Coordinates 1)) (⊤ : Opens (TopCat.of (Coordinates 1)))
    (0 : TopCat.of (Coordinates 1)) trivial
    (toSheafify (Opens.grothendieckTopology (Coordinates 1)) (quotientPresheaf 1 doublePoint))
    (Ideal.Quotient.mk (analyticIdeal 1 doublePoint ⊤) (polynomialSections 1 ⊤ (MvPolynomial.X 0)))
  have h' := (key.trans h).trans (map_zero (ConcreteCategory.hom
    ((TopCat.Presheaf.stalkFunctor CommRingCat (0 : TopCat.of (Coordinates 1))).map
      (toSheafify (Opens.grothendieckTopology (Coordinates 1))
        (quotientPresheaf 1 doublePoint))))).symm
  have hbij := ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor CommRingCat (0 : TopCat.of (Coordinates 1))).map
      (toSheafify (Opens.grothendieckTopology (Coordinates 1)) (quotientPresheaf 1 doublePoint)))
  exact presheaf_germ_coordinate_ne_zero (hbij.1 h')

private theorem origin_mem_zeroSet : (0 : Coordinates 1) ∈ zeroSet 1 doublePoint := by
  intro f hf
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hf
  simp

/-- The nilpotent `z` survives in the double-point analytic space itself: its image in the global
sections of the structure sheaf (the inverse image of `𝒪/(z²)` on the zero set) is nonzero. -/
private theorem polynomialMap_coordinate_ne_zero :
    polynomialMap 1 doublePoint (MvPolynomial.X 0) ≠ 0 := by
  classical
  intro h
  let i := inclusion 1 doublePoint
  let x : TopCat.of (zeroSet 1 doublePoint) := ⟨0, origin_mem_zeroSet⟩
  let F := quotientSheaf 1 doublePoint
  let A := TopCat.Presheaf.stalk (X := TopCat.of (Coordinates 1)) F.obj (i x)
  let G : TopCat.Sheaf CommRingCat (TopCat.of (zeroSet 1 doublePoint)) := skyscraperSheaf x A
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat i
  let ψ : F ⟶ (TopCat.Sheaf.pushforward CommRingCat i).obj G :=
    ⟨StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf (p₀ := i x) (𝟙 A)⟩
  have hψ : ψ = adj.unit.app F ≫ (TopCat.Sheaf.pushforward CommRingCat i).map
      ((adj.homEquiv F G).symm ψ) := by
    conv_lhs => rw [← (adj.homEquiv F G).apply_symm_apply ψ]
    exact adj.homEquiv_unit F G _
  let s := (toSheafify (Opens.grothendieckTopology (Coordinates 1))
    (quotientPresheaf 1 doublePoint)).app (op ⊤)
      (Ideal.Quotient.mk (analyticIdeal 1 doublePoint ⊤)
        (polynomialSections 1 ⊤ (MvPolynomial.X 0)))
  have h0 : (ConcreteCategory.hom ((adj.unit.app F).hom.app (op ⊤))) s = 0 := h
  have h1 : (ConcreteCategory.hom (ψ.hom.app (op ⊤))) s =
      (ConcreteCategory.hom (((TopCat.Sheaf.pushforward CommRingCat i).map
        ((adj.homEquiv F G).symm ψ)).hom.app (op ⊤)))
          ((ConcreteCategory.hom ((adj.unit.app F).hom.app (op ⊤))) s) := by
    conv_lhs => rw [hψ]
    rfl
  rw [h0, map_zero] at h1
  have hmem : i x ∈ (⊤ : Opens (TopCat.of (Coordinates 1))) := trivial
  have e := StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk (i x)
    (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf (𝓕 := F.obj) (i x) (𝟙 A)) ⊤ hmem
  rw [StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper, Category.comp_id] at e
  have h3 := ConcreteCategory.congr_hom e s
  rw [ConcreteCategory.comp_apply] at h3
  have h4 : (ConcreteCategory.hom (TopCat.Presheaf.germ F.obj ⊤ (i x) hmem)) s = 0 := by
    have h1' : (ConcreteCategory.hom ((StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf
        (𝓕 := F.obj) (i x) (𝟙 A)).app (op ⊤))) s = 0 := h1
    rw [h3, h1', map_zero]
  exact sheaf_germ_coordinate_ne_zero h4

end GeneralAnalyticGeometryTest.DoublePoint
