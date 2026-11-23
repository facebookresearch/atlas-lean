/-
Copyright (c) 2025 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Algebra.Homology.QuasiIsoProjectiveSeparator
public import MathlibExt.AlgebraicTopology.SingularHomology.SingularSubdivision.Realization
public import MathlibExt.AlgebraicTopology.SingularHomology.SmallChains
public import MathlibExt.Topology.MetricSpace.CompactCover

/-!
# Small-chain quasi-isomorphism foundations

Coefficient-independent metric estimates for iterated singular subdivision.
-/

@[expose] public section

open scoped BigOperators
open CategoryTheory Limits Opposite Simplicial SimplexCategory SimplicialObject Matrix

namespace AlgebraicTopology

universe v u w z

/-- Diameter of `Set.univ` in a subtype coincides with the ambient diameter,
via the subtype isometry. -/
theorem diam_univ_subtype {V : Type w} [PseudoMetricSpace V] (K : Set V) :
    Metric.diam (Set.univ : Set K) = Metric.diam K := by
  rw [← isometry_subtype_coe.diam_image, Set.image_univ, Subtype.range_coe]

theorem affineRealize_range_diam_le {V : Type w}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} (τ : Fin (d + 1) → V) :
    Metric.diam (Set.range (affineRealize τ)) ≤
      Metric.diam (Set.range τ) := by
  have hsub :
      Set.range (affineRealize τ) ⊆ convexHull ℝ (Set.range τ) :=
    fun y ⟨x, hx⟩ => hx ▸ affineRealize_mem_convexHull τ x
  calc
    Metric.diam (Set.range (affineRealize τ)) ≤
        Metric.diam (convexHull ℝ (Set.range τ)) :=
      Metric.diam_mono hsub
        (isBounded_convexHull.mpr (Set.finite_range τ).isBounded)
    _ = Metric.diam (Set.range τ) := convexHull_diam _

/-- Diameter bound for `affineRealizeIn` over an arbitrary convex set in an
arbitrary universe: the image diameter is at most that of the spanning
vertices, via the subtype isometry. -/
theorem affineRealizeIn_range_diam_le_of_convex
    {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set V} (hK : Convex ℝ K) {d : ℕ}
    (τ : Fin (d + 1) → V) (hτ : ∀ i, τ i ∈ K) :
    Metric.diam (Set.range (affineRealizeIn K hK τ hτ)) ≤
      Metric.diam (Set.range τ) := by
  have hiso : Isometry (Subtype.val : K → V) := isometry_subtype_coe
  have heq :
      Subtype.val '' Set.range (affineRealizeIn K hK τ hτ) =
        Set.range (affineRealize τ) := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨affineRealizeIn K hK τ hτ x, ⟨x, rfl⟩, rfl⟩
  calc
    Metric.diam (Set.range (affineRealizeIn K hK τ hτ)) =
        Metric.diam (Subtype.val '' Set.range (affineRealizeIn K hK τ hτ)) :=
      (hiso.diam_image _).symm
    _ = Metric.diam (Set.range (affineRealize τ)) := by rw [heq]
    _ ≤ Metric.diam (Set.range τ) := affineRealize_range_diam_le τ

section SmallChainFactorization

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
variable {X : TopCat.{w}} {ι : Type*}

def FactorsThroughSmallChainInclusion (R : C) (U : ι → Set X) (n : ℕ)
    {A : C} (f : A ⟶ (sChain X R).X n) : Prop :=
  ∃ g : A ⟶ (smallChainComplex (C := C) R U).X n,
    g ≫ (smallChainInclusion (C := C) R U).f n = f

lemma factors_zero (R : C) (U : ι → Set X) (n : ℕ) {A : C} :
    FactorsThroughSmallChainInclusion (C := C) R U n
      (0 : A ⟶ (sChain X R).X n) :=
  ⟨0, by simp⟩

lemma factors_add (R : C) (U : ι → Set X) (n : ℕ) {A : C}
    {f g : A ⟶ (sChain X R).X n}
    (hf : FactorsThroughSmallChainInclusion (C := C) R U n f)
    (hg : FactorsThroughSmallChainInclusion (C := C) R U n g) :
    FactorsThroughSmallChainInclusion R U n (f + g) := by
  obtain ⟨gf, hgf⟩ := hf
  obtain ⟨gg, hgg⟩ := hg
  exact ⟨gf + gg, by rw [Preadditive.add_comp, hgf, hgg]⟩

lemma factors_neg (R : C) (U : ι → Set X) (n : ℕ) {A : C}
    {f : A ⟶ (sChain X R).X n}
    (hf : FactorsThroughSmallChainInclusion (C := C) R U n f) :
    FactorsThroughSmallChainInclusion R U n (-f) := by
  obtain ⟨g, hg⟩ := hf
  exact ⟨-g, by rw [Preadditive.neg_comp, hg]⟩

lemma chainSpan_factors {V : Type z} [HasCoproducts.{z} C] (R : C) (U : ι → Set X) {n m : ℕ}
    {Y : Set (Fin (n + 1) → V)}
    {f : (freemod (C := C) R V).obj (Opposite.op ⦋n⦌) ⟶
      (sChain X R).X m}
    (hf : ∀ τ ∈ Y,
      FactorsThroughSmallChainInclusion (C := C) R U m
        (Sigma.ι (fun _ : Fin (n + 1) → V => (R : C)) τ ≫ f))
    {c : R ⟶ (freemod (C := C) R V).obj (Opposite.op ⦋n⦌)}
    (hc : c ∈ chainSpan (C := C) R n Y) :
    FactorsThroughSmallChainInclusion R U m (c ≫ f) := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨τ, hτ, rfl⟩ := hx
    exact hf τ hτ
  | zero =>
    have h0 : (0 : R ⟶ _) ≫ f = (0 : R ⟶ _) := by simp
    rw [h0]
    exact factors_zero (C := C) R U m
  | add x y _ _ ihx ihy =>
    have hAdd : FactorsThroughSmallChainInclusion (C := C) R U m
        (x ≫ f + y ≫ f) :=
      factors_add R U m ihx ihy
    have heq : (x + y) ≫ f = x ≫ f + y ≫ f := by
      simp [Preadditive.add_comp]
    rw [← heq] at hAdd
    exact hAdd
  | neg x _ ihx =>
    have hNeg : FactorsThroughSmallChainInclusion (C := C) R U m
        (-(x ≫ f)) :=
      factors_neg R U m ihx
    have heq : (-x) ≫ f = -(x ≫ f) := by
      simp [Preadditive.neg_comp]
    rw [← heq] at hNeg
    exact hNeg

lemma factors_of_mem_subordinateCover (R : C) (U : ι → Set X) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌))
    (hσ : σ ∈ (subordinateCover U).obj (Opposite.op ⦋n⦌)) :
    FactorsThroughSmallChainInclusion (C := C) R U n
      ((TopCat.toSSet.obj X).ιChainComplex (R := R) σ) := by
  refine ⟨(subordinateCover (X := X) U).toSSet.ιChainComplex (R := R)
      (⟨σ, hσ⟩ : (subordinateCover U).toSSet.obj (Opposite.op ⦋n⦌)), ?_⟩
  have h := SSet.ι_chainComplexMap_f
      (X := (subordinateCover U).toSSet)
      (Y := TopCat.toSSet.obj X) ((subordinateCover U).ι) (R := R)
      (⟨σ, hσ⟩ : (subordinateCover U).toSSet.obj (Opposite.op ⦋n⦌))
  simpa using h

noncomputable def smallChainLiftOfFactors
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)
    (n m : ℕ) (T : (sChain X R).X n ⟶ (sChain X R).X m)
    (hT : ∀ σ : (subordinateCover U).toSSet.obj (Opposite.op ⦋n⦌),
      FactorsThroughSmallChainInclusion R U m
        (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ.1 ≫ T)) :
    (smallChainComplex (C := C) R U).X n ⟶
      (smallChainComplex (C := C) R U).X m :=
  Sigma.desc fun σ => Classical.choose (hT σ)

theorem smallChainLiftOfFactors_comp_inclusion
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)
    (n m : ℕ) (T : (sChain X R).X n ⟶ (sChain X R).X m)
    (hT : ∀ σ : (subordinateCover U).toSSet.obj (Opposite.op ⦋n⦌),
      FactorsThroughSmallChainInclusion R U m
        (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ.1 ≫ T)) :
    smallChainLiftOfFactors R U n m T hT ≫
        (smallChainInclusion (C := C) R U).f m =
      (smallChainInclusion (C := C) R U).f n ≫ T := by
  apply SSet.chainComplex_hom_ext (X := (subordinateCover U).toSSet) (R := R) (n := n)
  intro σ
  have hLift : Sigma.ι (fun _ : (subordinateCover U).toSSet.obj (Opposite.op ⦋n⦌) => R) σ ≫
      smallChainLiftOfFactors R U n m T hT = Classical.choose (hT σ) := by
    change Sigma.ι
        (fun _ : (subordinateCover U).toSSet.obj (Opposite.op ⦋n⦌) => R) σ ≫
      Sigma.desc (fun τ => Classical.choose (hT τ)) = _
    exact Sigma.ι_comp_desc _ _
  have hInc : Sigma.ι (fun _ : (subordinateCover U).toSSet.obj (Opposite.op ⦋n⦌) => R) σ ≫
      (smallChainInclusion (C := C) R U).f n =
        SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ.1 := by
    exact SSet.ι_chainComplexMap_f
      (X := (subordinateCover U).toSSet)
      (Y := TopCat.toSSet.obj X) ((subordinateCover U).ι) (R := R) σ
  calc Sigma.ι (fun _ : (subordinateCover U).toSSet.obj (Opposite.op ⦋n⦌) => R) σ ≫
        smallChainLiftOfFactors R U n m T hT ≫ (smallChainInclusion (C := C) R U).f m
      = (Sigma.ι (fun _ : (subordinateCover U).toSSet.obj (Opposite.op ⦋n⦌) => R) σ ≫
          smallChainLiftOfFactors R U n m T hT) ≫ (smallChainInclusion (C := C) R U).f m :=
        (Category.assoc _ _ _).symm
    _ = Classical.choose (hT σ) ≫ (smallChainInclusion (C := C) R U).f m :=
        congrArg (· ≫ (smallChainInclusion (C := C) R U).f m) hLift
    _ = SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ.1 ≫ T :=
        (hT σ).choose_spec
    _ = (Sigma.ι (fun _ : (subordinateCover U).toSSet.obj (Opposite.op ⦋n⦌) => R) σ ≫
          (smallChainInclusion (C := C) R U).f n) ≫ T :=
        congrArg (· ≫ T) hInc.symm
    _ = Sigma.ι (fun _ : (subordinateCover U).toSSet.obj (Opposite.op ⦋n⦌) => R) σ ≫
          (smallChainInclusion (C := C) R U).f n ≫ T :=
        Category.assoc _ _ _

theorem smallChainInclusion_naturality_coefficient_f
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)
    (q : ℕ) :
    (((SSet.chainComplexFunctor C).map a).app
        (subordinateCover U).toSSet).f q ≫
        (smallChainInclusion (C := C) S U).f q =
      (smallChainInclusion (C := C) R U).f q ≫
        (((SSet.chainComplexFunctor C).map a).app
          (TopCat.toSSet.obj X)).f q := by
  have h := (smallChainInclusionNatTrans C U).naturality a
  change (((SSet.chainComplexFunctor C).map a).app
        (subordinateCover U).toSSet) ≫
        (smallChainInclusion (C := C) S U) =
      (smallChainInclusion (C := C) R U) ≫
        (((SSet.chainComplexFunctor C).map a).app
          (TopCat.toSSet.obj X)) at h
  exact congrArg (fun φ => φ.f q) h

theorem smallChainLiftOfFactors_naturality_coefficient_comp_inclusion
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) {X : TopCat.{w}} {ι : Type z} (U : ι → Set X)
    (n m : ℕ)
    (T_R : (sChain X R).X n ⟶ (sChain X R).X m)
    (T_S : (sChain X S).X n ⟶ (sChain X S).X m)
    (hT_R : ∀ σ : (subordinateCover U).toSSet.obj
        (Opposite.op (SimplexCategory.mk n)),
      FactorsThroughSmallChainInclusion R U m
        (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ.1 ≫ T_R))
    (hT_S : ∀ σ : (subordinateCover U).toSSet.obj
        (Opposite.op (SimplexCategory.mk n)),
      FactorsThroughSmallChainInclusion S U m
        (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := S) σ.1 ≫ T_S))
    (hT : (((SSet.chainComplexFunctor C).map a).app
        (TopCat.toSSet.obj X)).f n ≫ T_S =
      T_R ≫ (((SSet.chainComplexFunctor C).map a).app
        (TopCat.toSSet.obj X)).f m) :
    ((((SSet.chainComplexFunctor C).map a).app
          (subordinateCover U).toSSet).f n ≫
        smallChainLiftOfFactors S U n m T_S hT_S) ≫
        (smallChainInclusion (C := C) S U).f m =
      (smallChainLiftOfFactors R U n m T_R hT_R ≫
        (((SSet.chainComplexFunctor C).map a).app
          (subordinateCover U).toSSet).f m) ≫
        (smallChainInclusion (C := C) S U).f m := by
  rw [Category.assoc, smallChainLiftOfFactors_comp_inclusion]
  rw [← Category.assoc,
    smallChainInclusion_naturality_coefficient_f]
  rw [Category.assoc, hT]
  rw [← Category.assoc,
    ← smallChainLiftOfFactors_comp_inclusion]
  rw [Category.assoc, Category.assoc,
    smallChainInclusion_naturality_coefficient_f]

theorem smallChainLiftOfFactors_naturality_coefficient
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) {X : TopCat.{w}} {ι : Type z} (U : ι → Set X)
    (n m : ℕ)
    (T_R : (sChain X R).X n ⟶ (sChain X R).X m)
    (T_S : (sChain X S).X n ⟶ (sChain X S).X m)
    (hT_R : ∀ σ : (subordinateCover U).toSSet.obj
        (Opposite.op (SimplexCategory.mk n)),
      FactorsThroughSmallChainInclusion R U m
        (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ.1 ≫ T_R))
    (hT_S : ∀ σ : (subordinateCover U).toSSet.obj
        (Opposite.op (SimplexCategory.mk n)),
      FactorsThroughSmallChainInclusion S U m
        (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := S) σ.1 ≫ T_S))
    (hT : (((SSet.chainComplexFunctor C).map a).app
        (TopCat.toSSet.obj X)).f n ≫ T_S =
      T_R ≫ (((SSet.chainComplexFunctor C).map a).app
        (TopCat.toSSet.obj X)).f m) :
    (((SSet.chainComplexFunctor C).map a).app
          (subordinateCover U).toSSet).f n ≫
        smallChainLiftOfFactors S U n m T_S hT_S =
      smallChainLiftOfFactors R U n m T_R hT_R ≫
        (((SSet.chainComplexFunctor C).map a).app
          (subordinateCover U).toSSet).f m := by
  apply (cancel_mono (f := (smallChainInclusion (C := C) S U).f m)).mp
  exact smallChainLiftOfFactors_naturality_coefficient_comp_inclusion
    a U n m T_R T_S hT_R hT_S hT

end SmallChainFactorization

section SubordinateMem

variable {X : TopCat.{w}} {ι : Type*} {U : ι → Set X}

lemma mem_subordinateCover_of_range_sub {n : ℕ}
    {σ : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)} {i : ι}
    (h : Set.range (X.toSSetObjEquiv (Opposite.op ⦋n⦌) σ) ⊆ U i) :
    σ ∈ (subordinateCover (X := X) U).obj (Opposite.op ⦋n⦌) := by
  have hmem : σ ∈ (subordinateSet (U i)).obj (Opposite.op ⦋n⦌) := h
  have hle : subordinateSet (U i) ≤ subordinateCover (X := X) U :=
    le_iSup (fun j => subordinateSet (U j)) i
  exact hle _ hmem

end SubordinateMem

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem chainSpan_realizeIn_factorsULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat.{w}) {ι : Type*} (U : ι → Set X)
    {n m : ℕ} (f : SimplexCategory.toTop.{w}.obj ⦋n⦌ ⟶ X)
    {Y : Set (Fin (m + 1) → ULift.{w} (Fin (n + 1) → ℝ))}
    (hY : ∀ τ ∈ Y, ∀ i, τ i ∈ liftedStdSimplex.{w} n)
    (hImage : ∀ τ (hτ : τ ∈ Y), ∃ i,
      Set.range ((f.hom.comp (liftedStdSimplexTopHom.{w} n).hom).comp
        (affineRealizeIn (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n) τ (hY τ hτ))) ⊆ U i)
    {c : R ⟶ (freemod (C := C) R
      (ULift.{w} (Fin (n + 1) → ℝ))).obj (Opposite.op ⦋m⦌)}
    (hc : c ∈ chainSpan (C := C) R m Y) :
    FactorsThroughSmallChainInclusion (C := C) R U m
      (c ≫ liftIn (R := R) (liftedStdSimplex.{w} n) m ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f m ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f m ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map f)).f m) := by
  apply chainSpan_factors (C := C) R U (Y := Y) (f :=
    liftIn (R := R) (liftedStdSimplex.{w} n) m ≫
      (realizeInChain (R := R) (liftedStdSimplex.{w} n)
        (convex_liftedStdSimplex.{w} n)).f m ≫
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f m ≫
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map f)).f m) ?_ hc
  intro τ hτ
  let στ : (linSSetIn (ULift.{w} (Fin (n + 1) → ℝ))
        (liftedStdSimplex.{w} n)).obj (Opposite.op ⦋m⦌) :=
    ⟨τ, hY τ hτ⟩
  have hι : Sigma.ι
        (fun _ : Fin (m + 1) → ULift.{w} (Fin (n + 1) → ℝ) => R) τ ≫
        (liftIn (R := R) (liftedStdSimplex.{w} n) m ≫
          (realizeInChain (R := R) (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)).f m ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f m ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map f)).f m) =
      SSet.ιChainComplex
          (X := linSSetIn (ULift.{w} (Fin (n + 1) → ℝ))
            (liftedStdSimplex.{w} n)) (R := R) στ ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f m ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f m ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map f)).f m := by
    have hChange : Sigma.ι
          (fun _ : Fin (m + 1) → ULift.{w} (Fin (n + 1) → ℝ) => R) τ =
        SSet.ιChainComplex
          (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R) τ := rfl
    rw [hChange]
    erw [liftIn_ι_assoc (R := R), dite_eq_left (hY τ hτ)]
  have hReal : SSet.ιChainComplex
          (X := linSSetIn (ULift.{w} (Fin (n + 1) → ℝ))
            (liftedStdSimplex.{w} n)) (R := R) στ ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f m ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f m ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map f)).f m =
      SSet.ιChainComplex
          (X := TopCat.toSSet.obj (TopCat.of (liftedStdSimplex.{w} n))) (R := R)
          ((realizeInNatTrans (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)).app (Opposite.op ⦋m⦌) στ) ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f m ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map f)).f m := by
    erw [realizeInChain_ι_assoc (R := R)]
  have hMapLift : SSet.ιChainComplex
          (X := TopCat.toSSet.obj (TopCat.of (liftedStdSimplex.{w} n))) (R := R)
          ((realizeInNatTrans (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)).app (Opposite.op ⦋m⦌) στ) ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f m ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map f)).f m =
      SSet.ιChainComplex
          (X := TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n⦌)) (R := R)
          ((TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n)).app
            (Opposite.op ⦋m⦌)
            ((realizeInNatTrans (liftedStdSimplex.{w} n)
              (convex_liftedStdSimplex.{w} n)).app (Opposite.op ⦋m⦌) στ)) ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map f)).f m := by
    erw [SSet.ι_chainComplexMap_f_assoc (R := R)]
  have hMap : SSet.ιChainComplex
          (X := TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n⦌)) (R := R)
          ((TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n)).app
            (Opposite.op ⦋m⦌)
            ((realizeInNatTrans (liftedStdSimplex.{w} n)
              (convex_liftedStdSimplex.{w} n)).app (Opposite.op ⦋m⦌) στ)) ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map f)).f m =
      SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R)
        ((TopCat.toSSet.map f).app (Opposite.op ⦋m⦌)
          ((TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n)).app
            (Opposite.op ⦋m⦌)
            ((realizeInNatTrans (liftedStdSimplex.{w} n)
              (convex_liftedStdSimplex.{w} n)).app (Opposite.op ⦋m⦌) στ))) := by
    erw [SSet.ι_chainComplexMap_f (R := R)]
  rw [hι, hReal, hMapLift, hMap]
  obtain ⟨i, hi⟩ := hImage τ hτ
  apply factors_of_mem_subordinateCover (C := C) R U m
  apply mem_subordinateCover_of_range_sub (i := i)
  exact hi

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every singular simplex becomes subordinate after sufficiently many
iterations of the universe-polymorphic subdivision operator. -/
theorem exists_iterate_simplex_factorsULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (X : TopCat.{w}) {ι : Type*} (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (Set.univ : Set X) ⊆ ⋃ i, U i) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) :
    ∃ k, FactorsThroughSmallChainInclusion (C := C) R U n
      (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
        (genericSingSubdivIterHomULift R X k).f n) := by
  let f : SimplexCategory.toTop.{w}.obj ⦋n⦌ ⟶ X :=
    TopCat.toSSetTopHom X (Opposite.op ⦋n⦌) σ
  let g : C(liftedStdSimplex.{w} n, X) :=
    f.hom.comp (liftedStdSimplexTopHom.{w} n).hom
  let : CompactSpace (liftedStdSimplex.{w} n) :=
    Homeomorph.compactSpace (liftedStdSimplexHomeo.{w} n).symm
  have hq0 : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have hq1 : (n : ℝ) / ((n : ℝ) + 1) < 1 := by
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    rw [div_lt_one hpos]
    linarith
  have hC : 0 ≤ Metric.diam (Set.univ : Set (liftedStdSimplex.{w} n)) :=
    Metric.diam_nonneg
  obtain ⟨k, hk⟩ :=
    Metric.exists_pow_mul_diam_subordinate_of_compact
      ((n : ℝ) / ((n : ℝ) + 1))
      (Metric.diam (Set.univ : Set (liftedStdSimplex.{w} n)))
      hq0 hq1 hC g U hUopen hUcover
  refine ⟨k, ?_⟩
  have hσ : SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
      (genericSingSubdivIterHomULift R X k).f n =
      univIterChainULift (C := C) R n k ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map f)).f n :=
    sigma_ι_genericSingSubdivIterULift R n k X σ
  have huniv := univIterChainULift_eq (C := C) R n k
  let c : R ⟶ (freemod (C := C) R
        (ULift.{w} (Fin (n + 1) → ℝ))).obj (Opposite.op ⦋n⦌) :=
    Sigma.ι
        (fun _ : Fin (n + 1) → ULift.{w} (Fin (n + 1) → ℝ) => R)
        (liftedStdAffine.{w} n) ≫
      subdivIter (C := C) (W := ULift.{w} (Fin (n + 1) → ℝ)) R n k
  have hc : c ∈ chainSpan (C := C) R n
      (subdivIterSimplices k (liftedStdAffine.{w} n)) :=
    subdivIter_mem_chainSpan (C := C) R n k (liftedStdAffine.{w} n)
  have hY : ∀ τ ∈ subdivIterSimplices k (liftedStdAffine.{w} n),
      ∀ i, τ i ∈ liftedStdSimplex.{w} n := by
    intro τ hτ i
    exact (convexHull_min
      (Set.range_subset_iff.mpr
        (liftedStdAffine_mem_liftedStdSimplex.{w} n))
      (convex_liftedStdSimplex.{w} n))
        (hτ.1 (Set.mem_range_self i))
  have hKcompact : IsCompact (liftedStdSimplex.{w} n) :=
    isCompact_iff_compactSpace.mpr inferInstance
  have hImage : ∀ τ (hτ : τ ∈ subdivIterSimplices k (liftedStdAffine.{w} n)), ∃ i,
      Set.range (g.comp
        (affineRealizeIn (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n) τ (hY τ hτ))) ⊆ U i := by
    intro τ hτ
    have hDiam : Metric.diam (Set.range
        (affineRealizeIn (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n) τ (hY τ hτ))) ≤
        ((n : ℝ) / ((n : ℝ) + 1)) ^ k *
          Metric.diam (Set.univ : Set (liftedStdSimplex.{w} n)) := by
      calc
        Metric.diam (Set.range
            (affineRealizeIn (liftedStdSimplex.{w} n)
              (convex_liftedStdSimplex.{w} n) τ (hY τ hτ))) ≤
            Metric.diam (Set.range τ) :=
          affineRealizeIn_range_diam_le_of_convex
            (convex_liftedStdSimplex.{w} n) τ (hY τ hτ)
        _ ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ k *
            Metric.diam (Set.range (liftedStdAffine.{w} n)) := hτ.2
        _ ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ k *
            Metric.diam (liftedStdSimplex.{w} n) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Metric.diam_mono
            (fun y hy => by
              obtain ⟨j, rfl⟩ := hy
              exact liftedStdAffine_mem_liftedStdSimplex.{w} n j)
            hKcompact.isBounded
        _ = ((n : ℝ) / ((n : ℝ) + 1)) ^ k *
            Metric.diam (Set.univ : Set (liftedStdSimplex.{w} n)) := by
          rw [diam_univ_subtype]
    obtain ⟨i, hi⟩ := hk _ (Set.range_nonempty _) hDiam
    exact ⟨i, by simpa [ContinuousMap.coe_comp, Set.range_comp] using hi⟩
  have hChain := chainSpan_realizeIn_factorsULift
    (C := C) R X U f hY hImage hc
  have hAssoc : SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
      (genericSingSubdivIterHomULift R X k).f n =
      c ≫ liftIn (R := R) (liftedStdSimplex.{w} n) n ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f n ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f n ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map f)).f n := by
    rw [hσ, huniv]
    dsimp [c]
    simp only [Category.assoc]
    rfl
  rw [hAssoc]
  exact hChain

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Subdivision of a subordinate singular simplex factors through the
small-chain inclusion in an arbitrary universe. -/
theorem smallChain_iterate_factorsULift {C : Type u} [Category.{v} C]
    [Preadditive C] [HasCoproducts.{w} C] (R : C) (X : TopCat.{w})
    {ι : Type*} (U : ι → Set X) (n k : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌))
    (hσ : σ ∈ (subordinateCover (X := X) U).obj (Opposite.op ⦋n⦌)) :
    FactorsThroughSmallChainInclusion (C := C) R U n
      (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
        (genericSingSubdivIterHomULift R X k).f n) := by
  let f : SimplexCategory.toTop.{w}.obj ⦋n⦌ ⟶ X :=
    TopCat.toSSetTopHom X (Opposite.op ⦋n⦌) σ
  let g : C(liftedStdSimplex.{w} n, X) :=
    f.hom.comp (liftedStdSimplexTopHom.{w} n).hom
  have hσEq : SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
      (genericSingSubdivIterHomULift R X k).f n =
      univIterChainULift (C := C) R n k ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map f)).f n :=
    sigma_ι_genericSingSubdivIterULift R n k X σ
  have huniv := univIterChainULift_eq (C := C) R n k
  let c : R ⟶ (freemod (C := C) R
        (ULift.{w} (Fin (n + 1) → ℝ))).obj (Opposite.op ⦋n⦌) :=
    Sigma.ι
        (fun _ : Fin (n + 1) → ULift.{w} (Fin (n + 1) → ℝ) => R)
        (liftedStdAffine.{w} n) ≫
      subdivIter (C := C) (W := ULift.{w} (Fin (n + 1) → ℝ)) R n k
  have hc : c ∈ chainSpan (C := C) R n
      (subdivIterSimplices k (liftedStdAffine.{w} n)) :=
    subdivIter_mem_chainSpan (C := C) R n k (liftedStdAffine.{w} n)
  have hY : ∀ τ ∈ subdivIterSimplices k (liftedStdAffine.{w} n),
      ∀ i, τ i ∈ liftedStdSimplex.{w} n := by
    intro τ hτ i
    exact (convexHull_min
      (Set.range_subset_iff.mpr
        (liftedStdAffine_mem_liftedStdSimplex.{w} n))
      (convex_liftedStdSimplex.{w} n))
        (hτ.1 (Set.mem_range_self i))
  have hCover : ∃ i, Set.range g ⊆ U i := by
    have hEq : (subordinateCover (X := X) U).obj (Opposite.op ⦋n⦌) =
        ⋃ i, (subordinateSet (U i)).obj (Opposite.op ⦋n⦌) := by
      ext x
      simp [subordinateCover]
    rw [hEq] at hσ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hσ
    refine ⟨i, ?_⟩
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    apply hi
    exact ⟨(liftedStdSimplexHomeo.{w} n x).down, rfl⟩
  have hImage : ∀ τ (hτ : τ ∈ subdivIterSimplices k (liftedStdAffine.{w} n)), ∃ i,
      Set.range (g.comp
        (affineRealizeIn (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n) τ (hY τ hτ))) ⊆ U i := by
    intro τ hτ
    obtain ⟨i, hi⟩ := hCover
    refine ⟨i, ?_⟩
    rw [ContinuousMap.coe_comp, Set.range_comp]
    exact Set.image_mono (Set.subset_univ _) |>.trans
      (by simpa [Set.image_univ, Set.range] using hi)
  have hChain := chainSpan_realizeIn_factorsULift
    (C := C) R X U f hY hImage hc
  have hAssoc : SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
      (genericSingSubdivIterHomULift R X k).f n =
      c ≫ liftIn (R := R) (liftedStdSimplex.{w} n) n ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f n ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f n ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map f)).f n := by
    rw [hσEq, huniv]
    dsimp [c]
    simp only [Category.assoc]
    rfl
  rw [hAssoc]
  exact hChain

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The subdivision homotopy on a subordinate singular simplex factors through
the small-chain inclusion in an arbitrary universe. -/
theorem smallChain_homotopy_factorsULift {C : Type u} [Category.{v} C]
    [Preadditive C] [HasCoproducts.{w} C] (R : C) (X : TopCat.{w})
    {ι : Type*} (U : ι → Set X) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌))
    (hσ : σ ∈ (subordinateCover (X := X) U).obj (Opposite.op ⦋n⦌)) :
    FactorsThroughSmallChainInclusion (C := C) R U (n + 1)
      (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
        genericSingHomotopyULift R X n) := by
  let f : SimplexCategory.toTop.{w}.obj ⦋n⦌ ⟶ X :=
    TopCat.toSSetTopHom X (Opposite.op ⦋n⦌) σ
  let g : C(liftedStdSimplex.{w} n, X) :=
    f.hom.comp (liftedStdSimplexTopHom.{w} n).hom
  have hσEq : SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
      genericSingHomotopyULift R X n =
      univHomotopyULift (C := C) R n ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map f)).f (n + 1) :=
    genericSingHomotopyULift_ι R X n σ
  have huniv : univHomotopyULift (C := C) R n =
      Sigma.ι
          (fun _ : Fin (n + 1) → ULift.{w} (Fin (n + 1) → ℝ) => R)
          (liftedStdAffine.{w} n) ≫
        homotopyOp (C := C) R (ULift.{w} (Fin (n + 1) → ℝ)) n ≫
        liftIn (R := R) (liftedStdSimplex.{w} n) (n + 1) ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f (n + 1) ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f (n + 1) := rfl
  let c : R ⟶ (freemod (C := C) R
        (ULift.{w} (Fin (n + 1) → ℝ))).obj (Opposite.op ⦋n + 1⦌) :=
    Sigma.ι
        (fun _ : Fin (n + 1) → ULift.{w} (Fin (n + 1) → ℝ) => R)
        (liftedStdAffine.{w} n) ≫
      homotopyOp (C := C) R (ULift.{w} (Fin (n + 1) → ℝ)) n
  have hc : c ∈ chainSpan (C := C) R (n + 1)
      (hullSimplices (m := n + 1) (liftedStdAffine.{w} n)) :=
    homotopyOp_mem_chainSpan (C := C) R n (liftedStdAffine.{w} n)
  have hY : ∀ τ ∈ hullSimplices (m := n + 1) (liftedStdAffine.{w} n),
      ∀ i, τ i ∈ liftedStdSimplex.{w} n := by
    intro τ hτ i
    exact (convexHull_min
      (Set.range_subset_iff.mpr
        (liftedStdAffine_mem_liftedStdSimplex.{w} n))
      (convex_liftedStdSimplex.{w} n))
        (hτ (Set.mem_range_self i))
  have hCover : ∃ i, Set.range g ⊆ U i := by
    have hEq : (subordinateCover (X := X) U).obj (Opposite.op ⦋n⦌) =
        ⋃ i, (subordinateSet (U i)).obj (Opposite.op ⦋n⦌) := by
      ext x
      simp [subordinateCover]
    rw [hEq] at hσ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hσ
    refine ⟨i, ?_⟩
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    apply hi
    exact ⟨(liftedStdSimplexHomeo.{w} n x).down, rfl⟩
  have hImage :
      ∀ τ (hτ : τ ∈ hullSimplices (m := n + 1) (liftedStdAffine.{w} n)), ∃ i,
        Set.range (g.comp
          (affineRealizeIn (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n) τ (hY τ hτ))) ⊆ U i := by
    intro τ hτ
    obtain ⟨i, hi⟩ := hCover
    refine ⟨i, ?_⟩
    rw [ContinuousMap.coe_comp, Set.range_comp]
    exact Set.image_mono (Set.subset_univ _) |>.trans
      (by simpa [Set.image_univ, Set.range] using hi)
  have hChain := chainSpan_realizeIn_factorsULift
    (C := C) R X U f hY hImage hc
  have hAssoc : SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := R) σ ≫
      genericSingHomotopyULift R X n =
      c ≫ liftIn (R := R) (liftedStdSimplex.{w} n) (n + 1) ≫
        (realizeInChain (R := R) (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f (n + 1) ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f (n + 1) ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map f)).f (n + 1) := by
    rw [hσEq, huniv]
    dsimp [c]
    simp only [Category.assoc]
  rw [hAssoc]
  exact hChain

/-- The iterated subdivision endomorphism restricted to the small-chain
complex, in an arbitrary universe. -/
noncomputable def smallSubdivisionIterateLiftULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {X : TopCat.{w}} {ι : Type*} (R : C) (U : ι → Set X)
    (k n : ℕ) : (smallChainComplex (C := C) R U).X n ⟶
      (smallChainComplex (C := C) R U).X n :=
  smallChainLiftOfFactors R U n n
    ((genericSingSubdivIterHomULift R X k).f n)
    (fun σ => smallChain_iterate_factorsULift R X U n k σ.1 σ.2)

@[reassoc]
theorem smallSubdivisionIterateLiftULift_comp_inclusion
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {X : TopCat.{w}} {ι : Type*} (R : C) (U : ι → Set X)
    (k n : ℕ) :
    smallSubdivisionIterateLiftULift R U k n ≫
        (smallChainInclusion (C := C) R U).f n =
      (smallChainInclusion (C := C) R U).f n ≫
        (genericSingSubdivIterHomULift R X k).f n := by
  apply smallChainLiftOfFactors_comp_inclusion

/-- The subdivision homotopy restricted to the small-chain complex, in an
arbitrary universe. -/
noncomputable def smallHomotopyLiftULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {X : TopCat.{w}} {ι : Type*} (R : C) (U : ι → Set X) (n : ℕ) :
    (smallChainComplex (C := C) R U).X n ⟶
      (smallChainComplex (C := C) R U).X (n + 1) :=
  smallChainLiftOfFactors R U n (n + 1) (genericSingHomotopyULift R X n)
    (fun σ => smallChain_homotopy_factorsULift R X U n σ.1 σ.2)

@[reassoc]
theorem smallHomotopyLiftULift_comp_inclusion
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {X : TopCat.{w}} {ι : Type*} (R : C) (U : ι → Set X) (n : ℕ) :
    smallHomotopyLiftULift R U n ≫
        (smallChainInclusion (C := C) R U).f (n + 1) =
      (smallChainInclusion (C := C) R U).f n ≫
        genericSingHomotopyULift R X n := by
  apply smallChainLiftOfFactors_comp_inclusion

@[reassoc]
theorem smallSubdivisionIterateLiftULift_naturality_coefficient
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) {X : TopCat.{w}} {ι : Type z}
    (U : ι → Set X) (k n : ℕ) :
    (((SSet.chainComplexFunctor C).map a).app
        (subordinateCover U).toSSet).f n ≫
        smallSubdivisionIterateLiftULift S U k n =
      smallSubdivisionIterateLiftULift R U k n ≫
        (((SSet.chainComplexFunctor C).map a).app
          (subordinateCover U).toSSet).f n := by
  apply smallChainLiftOfFactors_naturality_coefficient
  exact congrArg (fun f => f.f n)
    (genericSingSubdivIterHomULift_naturality_coefficient a X k)

@[reassoc]
theorem smallHomotopyLiftULift_naturality_coefficient
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) {X : TopCat.{w}} {ι : Type z}
    (U : ι → Set X) (n : ℕ) :
    (((SSet.chainComplexFunctor C).map a).app
        (subordinateCover U).toSSet).f n ≫
        smallHomotopyLiftULift S U n =
      smallHomotopyLiftULift R U n ≫
        (((SSet.chainComplexFunctor C).map a).app
          (subordinateCover U).toSSet).f (n + 1) := by
  apply smallChainLiftOfFactors_naturality_coefficient
  exact (genericSingHomotopyULift_naturality_coefficient a X n).symm

@[reassoc]
theorem smallSubdivisionIterateLiftULift_naturality_space
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {X Y : TopCat.{w}} {ι κ : Type*} (R : C) (f : X ⟶ Y)
    (U : ι → Set X) (V : κ → Set Y)
    (h : (subordinateCover U).image (TopCat.toSSet.map f) ≤
      subordinateCover (X := Y) V) (k n : ℕ) :
    smallSubdivisionIterateLiftULift R U k n ≫
        (smallChainMapOfImageLE R f U V h).f n =
      (smallChainMapOfImageLE R f U V h).f n ≫
        smallSubdivisionIterateLiftULift R V k n := by
  apply (cancel_mono (f := (smallChainInclusion (C := C) R V).f n)).mp
  have hMap := congrArg (fun g => g.f n)
    (smallChainMapOfImageLE_comp_inclusion (C := C) R f U V h)
  simp only [HomologicalComplex.comp_f] at hMap
  have hNat := congrArg (fun g => g.f n)
    (genericSingSubdivIterHomULift_naturality R f k)
  simp only [HomologicalComplex.comp_f] at hNat
  calc
    (smallSubdivisionIterateLiftULift R U k n ≫
          (smallChainMapOfImageLE R f U V h).f n) ≫
        (smallChainInclusion R V).f n =
      smallSubdivisionIterateLiftULift R U k n ≫
        ((smallChainMapOfImageLE R f U V h).f n ≫
          (smallChainInclusion R V).f n) := Category.assoc _ _ _
    _ = smallSubdivisionIterateLiftULift R U k n ≫
        ((smallChainInclusion R U).f n ≫ (singularChainMap R f).f n) := by rw [hMap]
    _ = (smallSubdivisionIterateLiftULift R U k n ≫
          (smallChainInclusion R U).f n) ≫ (singularChainMap R f).f n :=
      (Category.assoc _ _ _).symm
    _ = ((smallChainInclusion R U).f n ≫
          (genericSingSubdivIterHomULift R X k).f n) ≫
        (singularChainMap R f).f n := by rw [smallSubdivisionIterateLiftULift_comp_inclusion]
    _ = (smallChainInclusion R U).f n ≫
        ((genericSingSubdivIterHomULift R X k).f n ≫
          (singularChainMap R f).f n) := Category.assoc _ _ _
    _ = (smallChainInclusion R U).f n ≫
        ((singularChainMap R f).f n ≫
          (genericSingSubdivIterHomULift R Y k).f n) := by rw [hNat]
    _ = ((smallChainInclusion R U).f n ≫ (singularChainMap R f).f n) ≫
        (genericSingSubdivIterHomULift R Y k).f n := (Category.assoc _ _ _).symm
    _ = ((smallChainMapOfImageLE R f U V h).f n ≫
          (smallChainInclusion R V).f n) ≫
        (genericSingSubdivIterHomULift R Y k).f n := by rw [hMap]
    _ = (smallChainMapOfImageLE R f U V h).f n ≫
        ((smallChainInclusion R V).f n ≫
          (genericSingSubdivIterHomULift R Y k).f n) := Category.assoc _ _ _
    _ = (smallChainMapOfImageLE R f U V h).f n ≫
        (smallSubdivisionIterateLiftULift R V k n ≫
          (smallChainInclusion R V).f n) := by
      rw [smallSubdivisionIterateLiftULift_comp_inclusion]
    _ = ((smallChainMapOfImageLE R f U V h).f n ≫
          smallSubdivisionIterateLiftULift R V k n) ≫
        (smallChainInclusion R V).f n := (Category.assoc _ _ _).symm

@[reassoc]
theorem smallHomotopyLiftULift_naturality_space
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {X Y : TopCat.{w}} {ι κ : Type*} (R : C) (f : X ⟶ Y)
    (U : ι → Set X) (V : κ → Set Y)
    (h : (subordinateCover U).image (TopCat.toSSet.map f) ≤
      subordinateCover (X := Y) V) (n : ℕ) :
    smallHomotopyLiftULift R U n ≫
        (smallChainMapOfImageLE R f U V h).f (n + 1) =
      (smallChainMapOfImageLE R f U V h).f n ≫
        smallHomotopyLiftULift R V n := by
  apply (cancel_mono (f := (smallChainInclusion (C := C) R V).f (n + 1))).mp
  have hMapSucc := congrArg (fun g => g.f (n + 1))
    (smallChainMapOfImageLE_comp_inclusion (C := C) R f U V h)
  have hMap := congrArg (fun g => g.f n)
    (smallChainMapOfImageLE_comp_inclusion (C := C) R f U V h)
  simp only [HomologicalComplex.comp_f] at hMapSucc hMap
  have hNat := genericSingHomotopyULift_naturality R f n
  calc
    (smallHomotopyLiftULift R U n ≫
          (smallChainMapOfImageLE R f U V h).f (n + 1)) ≫
        (smallChainInclusion R V).f (n + 1) =
      smallHomotopyLiftULift R U n ≫
        ((smallChainMapOfImageLE R f U V h).f (n + 1) ≫
          (smallChainInclusion R V).f (n + 1)) := Category.assoc _ _ _
    _ = smallHomotopyLiftULift R U n ≫
        ((smallChainInclusion R U).f (n + 1) ≫
          (singularChainMap R f).f (n + 1)) := by rw [hMapSucc]
    _ = (smallHomotopyLiftULift R U n ≫
          (smallChainInclusion R U).f (n + 1)) ≫
        (singularChainMap R f).f (n + 1) := (Category.assoc _ _ _).symm
    _ = ((smallChainInclusion R U).f n ≫ genericSingHomotopyULift R X n) ≫
        (singularChainMap R f).f (n + 1) := by rw [smallHomotopyLiftULift_comp_inclusion]
    _ = (smallChainInclusion R U).f n ≫
        (genericSingHomotopyULift R X n ≫
          (singularChainMap R f).f (n + 1)) := Category.assoc _ _ _
    _ = (smallChainInclusion R U).f n ≫
        ((singularChainMap R f).f n ≫ genericSingHomotopyULift R Y n) := by rw [hNat]
    _ = ((smallChainInclusion R U).f n ≫ (singularChainMap R f).f n) ≫
        genericSingHomotopyULift R Y n := (Category.assoc _ _ _).symm
    _ = ((smallChainMapOfImageLE R f U V h).f n ≫
          (smallChainInclusion R V).f n) ≫ genericSingHomotopyULift R Y n := by rw [hMap]
    _ = (smallChainMapOfImageLE R f U V h).f n ≫
        ((smallChainInclusion R V).f n ≫ genericSingHomotopyULift R Y n) :=
      Category.assoc _ _ _
    _ = (smallChainMapOfImageLE R f U V h).f n ≫
        (smallHomotopyLiftULift R V n ≫
          (smallChainInclusion R V).f (n + 1)) := by
      rw [smallHomotopyLiftULift_comp_inclusion]
    _ = ((smallChainMapOfImageLE R f U V h).f n ≫
          smallHomotopyLiftULift R V n) ≫
        (smallChainInclusion R V).f (n + 1) := (Category.assoc _ _ _).symm

/-- The iterated subdivision endomorphism of the small-chain complex, in an
arbitrary universe. -/
noncomputable def smallSubdivisionIterateHomULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {X : TopCat.{w}} {ι : Type z} (R : C) (U : ι → Set X) (k : ℕ) :
    smallChainComplex (C := C) R U ⟶ smallChainComplex (C := C) R U where
  f n := smallSubdivisionIterateLiftULift R U k n
  comm' i j hij := by
    apply (cancel_mono (f := (smallChainInclusion (C := C) R U).f j)).mp
    calc
      (smallSubdivisionIterateLiftULift R U k i ≫
            (smallChainComplex (C := C) R U).d i j) ≫
          (smallChainInclusion (C := C) R U).f j =
        smallSubdivisionIterateLiftULift R U k i ≫
          ((smallChainComplex (C := C) R U).d i j ≫
            (smallChainInclusion (C := C) R U).f j) := Category.assoc _ _ _
      _ = smallSubdivisionIterateLiftULift R U k i ≫
          ((smallChainInclusion (C := C) R U).f i ≫
            (sChain X R).d i j) := by
            rw [← (smallChainInclusion (C := C) R U).comm' i j hij]
      _ = (smallSubdivisionIterateLiftULift R U k i ≫
            (smallChainInclusion (C := C) R U).f i) ≫
          (sChain X R).d i j := (Category.assoc _ _ _).symm
      _ = ((smallChainInclusion (C := C) R U).f i ≫
            (genericSingSubdivIterHomULift R X k).f i) ≫
          (sChain X R).d i j := by
            rw [smallSubdivisionIterateLiftULift_comp_inclusion]
      _ = (smallChainInclusion (C := C) R U).f i ≫
          ((genericSingSubdivIterHomULift R X k).f i ≫
            (sChain X R).d i j) := Category.assoc _ _ _
      _ = (smallChainInclusion (C := C) R U).f i ≫
          ((sChain X R).d i j ≫
            (genericSingSubdivIterHomULift R X k).f j) := by
            rw [(genericSingSubdivIterHomULift R X k).comm' i j hij]
      _ = ((smallChainInclusion (C := C) R U).f i ≫
            (sChain X R).d i j) ≫
          (genericSingSubdivIterHomULift R X k).f j :=
            (Category.assoc _ _ _).symm
      _ = ((smallChainComplex (C := C) R U).d i j ≫
            (smallChainInclusion (C := C) R U).f j) ≫
          (genericSingSubdivIterHomULift R X k).f j := by
            rw [(smallChainInclusion (C := C) R U).comm' i j hij]
      _ = (smallChainComplex (C := C) R U).d i j ≫
          ((smallChainInclusion (C := C) R U).f j ≫
            (genericSingSubdivIterHomULift R X k).f j) := Category.assoc _ _ _
      _ = (smallChainComplex (C := C) R U).d i j ≫
          (smallSubdivisionIterateLiftULift R U k j ≫
            (smallChainInclusion (C := C) R U).f j) := by
            rw [smallSubdivisionIterateLiftULift_comp_inclusion]
      _ = ((smallChainComplex (C := C) R U).d i j ≫
            smallSubdivisionIterateLiftULift R U k j) ≫
          (smallChainInclusion (C := C) R U).f j :=
            (Category.assoc _ _ _).symm

@[simp]
theorem smallSubdivisionIterateHomULift_f
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {X : TopCat.{w}} {ι : Type z} (R : C) (U : ι → Set X)
    (k n : ℕ) :
    (smallSubdivisionIterateHomULift R U k).f n =
      smallSubdivisionIterateLiftULift R U k n := rfl

@[reassoc]
theorem smallSubdivisionIterateHomULift_comp_inclusion
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {X : TopCat.{w}} {ι : Type z} (R : C) (U : ι → Set X) (k : ℕ) :
    smallSubdivisionIterateHomULift R U k ≫
        smallChainInclusion (C := C) R U =
      smallChainInclusion (C := C) R U ≫
        genericSingSubdivIterHomULift R X k := by
  apply HomologicalComplex.hom_ext
  intro n
  exact smallSubdivisionIterateLiftULift_comp_inclusion R U k n

/-- Iterated small-chain subdivision, natural in the coefficient object. -/
noncomputable def smallSubdivisionIterateNatTransULift
    (C : Type u) [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {X : TopCat.{w}} {ι : Type z} (U : ι → Set X) (k : ℕ) :
    smallChainCoefficientFunctor C U ⟶ smallChainCoefficientFunctor C U where
  app R := smallSubdivisionIterateHomULift R U k
  naturality R S a := by
    apply HomologicalComplex.hom_ext
    intro n
    exact smallSubdivisionIterateLiftULift_naturality_coefficient a U k n

@[simp]
theorem smallSubdivisionIterateNatTransULift_app
    (C : Type u) [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {X : TopCat.{w}} {ι : Type z} (U : ι → Set X) (k : ℕ) (R : C) :
    (smallSubdivisionIterateNatTransULift C U k).app R =
      smallSubdivisionIterateHomULift R U k := rfl

@[reassoc]
theorem smallSubdivisionIterateHomULift_naturality_space
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {X Y : TopCat.{w}} {ι κ : Type*} (R : C) (f : X ⟶ Y)
    (U : ι → Set X) (V : κ → Set Y)
    (h : (subordinateCover U).image (TopCat.toSSet.map f) ≤
      subordinateCover (X := Y) V) (k : ℕ) :
    smallSubdivisionIterateHomULift R U k ≫
        smallChainMapOfImageLE R f U V h =
      smallChainMapOfImageLE R f U V h ≫
        smallSubdivisionIterateHomULift R V k := by
  apply HomologicalComplex.hom_ext
  intro n
  exact smallSubdivisionIterateLiftULift_naturality_space R f U V h k n

private lemma smallSubdivisionIterateLiftULift_one_comp_inclusion
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X : TopCat.{w}} {ι : Type z} (U : ι → Set X) (n : ℕ) :
    smallSubdivisionIterateLiftULift R U 1 n ≫
        (smallChainInclusion (C := C) R U).f n =
      (smallChainInclusion (C := C) R U).f n ≫
        (genericSingSubdivHomULift R X).f n := by
  have h := smallSubdivisionIterateLiftULift_comp_inclusion
    (R := R) (U := U) 1 n
  have hEq : (genericSingSubdivIterHomULift R X 1).f n =
      (genericSingSubdivHomULift R X).f n := by simp
  rw [hEq] at h
  exact h

/-- The iterated subdivision homotopy restricted degreewise to the small-chain
complex, in an arbitrary universe. -/
noncomputable def smallSubdivisionIterateHomotopyLiftULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X : TopCat.{w}} {ι : Type z} (U : ι → Set X)
    (k i j : ℕ) :
    (smallChainComplex (C := C) R U).X i ⟶
      (smallChainComplex (C := C) R U).X j :=
  match k with
  | 0 => 0
  | k + 1 =>
    smallSubdivisionIterateLiftULift R U 1 i ≫
        smallSubdivisionIterateHomotopyLiftULift R U k i j +
      if h : i + 1 = j then h ▸ smallHomotopyLiftULift R U i else 0

@[simp]
lemma smallSubdivisionIterateHomotopyLiftULift_zero
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X : TopCat.{w}} {ι : Type z} (U : ι → Set X) (i j : ℕ) :
    smallSubdivisionIterateHomotopyLiftULift R U 0 i j = 0 := rfl

lemma smallSubdivisionIterateHomotopyLiftULift_succ
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X : TopCat.{w}} {ι : Type z} (U : ι → Set X)
    (k i j : ℕ) :
    smallSubdivisionIterateHomotopyLiftULift R U (k + 1) i j =
      smallSubdivisionIterateLiftULift R U 1 i ≫
          smallSubdivisionIterateHomotopyLiftULift R U k i j +
        if h : i + 1 = j then h ▸ smallHomotopyLiftULift R U i else 0 := rfl

@[reassoc]
lemma smallSubdivisionIterateHomotopyLiftULift_comp_inclusion
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X : TopCat.{w}} {ι : Type z} (U : ι → Set X)
    (k i j : ℕ) :
    smallSubdivisionIterateHomotopyLiftULift R U k i j ≫
        (smallChainInclusion (C := C) R U).f j =
      (smallChainInclusion (C := C) R U).f i ≫
        (genericSingSubdivIterHomotopyULift R X k).hom i j := by
  induction k with
  | zero =>
    have h0 : genericSingSubdivIterHomotopyULift R X 0 =
        Homotopy.refl (𝟙 (sChain X R)) := rfl
    simp only [smallSubdivisionIterateHomotopyLiftULift_zero,
      zero_comp, h0, Homotopy.refl_hom, comp_zero]
  | succ k ih =>
    have h_one :
        (if h : i + 1 = j then h ▸ smallHomotopyLiftULift R U i else 0) ≫
            (smallChainInclusion (C := C) R U).f j =
        (smallChainInclusion (C := C) R U).f i ≫
          (genericSingSubdivHomotopyULift R X).hom i j := by
      by_cases hij : i + 1 = j
      · subst hij
        simp only [genericSingSubdivHomotopyULift,
          ↓reduceDIte, smallHomotopyLiftULift_comp_inclusion]
      · simp only [genericSingSubdivHomotopyULift, hij,
          ↓reduceDIte, zero_comp, comp_zero]
    calc
      smallSubdivisionIterateHomotopyLiftULift R U (k + 1) i j ≫
          (smallChainInclusion (C := C) R U).f j =
        (smallSubdivisionIterateLiftULift R U 1 i ≫
              smallSubdivisionIterateHomotopyLiftULift R U k i j +
            if h : i + 1 = j then h ▸ smallHomotopyLiftULift R U i else 0) ≫
          (smallChainInclusion (C := C) R U).f j := by
            rw [smallSubdivisionIterateHomotopyLiftULift_succ]
      _ = (smallSubdivisionIterateLiftULift R U 1 i ≫
              smallSubdivisionIterateHomotopyLiftULift R U k i j) ≫
            (smallChainInclusion (C := C) R U).f j +
          (if h : i + 1 = j then h ▸ smallHomotopyLiftULift R U i else 0) ≫
            (smallChainInclusion (C := C) R U).f j := by
            rw [Preadditive.add_comp]
      _ = smallSubdivisionIterateLiftULift R U 1 i ≫
            (smallSubdivisionIterateHomotopyLiftULift R U k i j ≫
              (smallChainInclusion (C := C) R U).f j) +
          (if h : i + 1 = j then h ▸ smallHomotopyLiftULift R U i else 0) ≫
            (smallChainInclusion (C := C) R U).f j := by
            rw [Category.assoc]
      _ = smallSubdivisionIterateLiftULift R U 1 i ≫
            ((smallChainInclusion (C := C) R U).f i ≫
              (genericSingSubdivIterHomotopyULift R X k).hom i j) +
          (smallChainInclusion (C := C) R U).f i ≫
            (genericSingSubdivHomotopyULift R X).hom i j := by
            rw [ih, h_one]
      _ = (smallSubdivisionIterateLiftULift R U 1 i ≫
            (smallChainInclusion (C := C) R U).f i) ≫
            (genericSingSubdivIterHomotopyULift R X k).hom i j +
          (smallChainInclusion (C := C) R U).f i ≫
            (genericSingSubdivHomotopyULift R X).hom i j := by
            rw [← Category.assoc]
      _ = ((smallChainInclusion (C := C) R U).f i ≫
            (genericSingSubdivHomULift R X).f i) ≫
            (genericSingSubdivIterHomotopyULift R X k).hom i j +
          (smallChainInclusion (C := C) R U).f i ≫
            (genericSingSubdivHomotopyULift R X).hom i j := by
            rw [smallSubdivisionIterateLiftULift_one_comp_inclusion]
      _ = (smallChainInclusion (C := C) R U).f i ≫
            ((genericSingSubdivHomULift R X).f i ≫
              (genericSingSubdivIterHomotopyULift R X k).hom i j) +
          (smallChainInclusion (C := C) R U).f i ≫
            (genericSingSubdivHomotopyULift R X).hom i j := by
            rw [Category.assoc]
      _ = (smallChainInclusion (C := C) R U).f i ≫
            ((genericSingSubdivHomULift R X).f i ≫
              (genericSingSubdivIterHomotopyULift R X k).hom i j +
            (genericSingSubdivHomotopyULift R X).hom i j) := by
            rw [Preadditive.comp_add]
      _ = (smallChainInclusion (C := C) R U).f i ≫
            (genericSingSubdivIterHomotopyULift R X (k + 1)).hom i j := by
            rw [← genericSingSubdivIterHomotopyULift_succ_component]

/-- The iterated small-chain subdivision is homotopic to the identity, in an
arbitrary universe. -/
noncomputable def smallSubdivisionIterateHomotopyULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X : TopCat.{w}} {ι : Type z} (U : ι → Set X) (k : ℕ) :
    Homotopy (𝟙 (smallChainComplex (C := C) R U))
      (smallSubdivisionIterateHomULift R U k) where
  hom := smallSubdivisionIterateHomotopyLiftULift R U k
  zero i j hij := by
    apply (cancel_mono (f := (smallChainInclusion (C := C) R U).f j)).mp
    rw [smallSubdivisionIterateHomotopyLiftULift_comp_inclusion]
    rw [(genericSingSubdivIterHomotopyULift R X k).zero i j hij]
    simp
  comm i := by
    apply (cancel_mono (f := (smallChainInclusion (C := C) R U).f i)).mp
    let H := genericSingSubdivIterHomotopyULift R X k
    have hHom :
        (fun p q => smallSubdivisionIterateHomotopyLiftULift R U k p q ≫
          (smallChainInclusion (C := C) R U).f q) =
        (fun p q => (smallChainInclusion (C := C) R U).f p ≫ H.hom p q) := by
      funext p q
      exact smallSubdivisionIterateHomotopyLiftULift_comp_inclusion R U k p q
    rw [Preadditive.add_comp, Preadditive.add_comp]
    rw [← dNext_comp_right, ← prevD_comp_right]
    rw [hHom]
    rw [dNext_comp_left, prevD_comp_left]
    rw [smallSubdivisionIterateHomULift_f,
      smallSubdivisionIterateLiftULift_comp_inclusion]
    rw [← Preadditive.comp_add, ← Preadditive.comp_add]
    rw [← H.comm i]
    simp

@[simp]
lemma smallSubdivisionIterateHomotopyULift_hom
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X : TopCat.{w}} {ι : Type z} (U : ι → Set X)
    (k i j : ℕ) :
    (smallSubdivisionIterateHomotopyULift R U k).hom i j =
      smallSubdivisionIterateHomotopyLiftULift R U k i j := rfl

/-- Iterated small-chain subdivision is a homotopy equivalence, in an arbitrary
universe. -/
noncomputable def smallSubdivisionIterateHomotopyEquivULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X : TopCat.{w}} {ι : Type z} (U : ι → Set X) (k : ℕ) :
    HomotopyEquiv (smallChainComplex (C := C) R U)
      (smallChainComplex (C := C) R U) where
  hom := smallSubdivisionIterateHomULift R U k
  inv := 𝟙 _
  homotopyHomInvId := by
    rw [Category.comp_id]
    exact (smallSubdivisionIterateHomotopyULift R U k).symm
  homotopyInvHomId := by
    rw [Category.id_comp]
    exact (smallSubdivisionIterateHomotopyULift R U k).symm

theorem smallSubdivisionIterateHomULift_homologyMap_eq_id
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X : TopCat.{w}} {ι : Type z} (U : ι → Set X)
    (k n : ℕ) [(smallChainComplex (C := C) R U).HasHomology n] :
    HomologicalComplex.homologyMap (smallSubdivisionIterateHomULift R U k) n =
      𝟙 ((smallChainComplex (C := C) R U).homology n) := by
  rw [← (smallSubdivisionIterateHomotopyULift R U k).homologyMap_eq n]
  exact HomologicalComplex.homologyMap_id
    (smallChainComplex (C := C) R U) n

/-- Once a morphism factors after `k` universe-polymorphic subdivision
iterations, it factors after any further number of iterations. -/
lemma factors_iterate_of_factorsULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {X : TopCat.{w}} {ι : Type*}
    (U : ι → Set X) (n k d : ℕ) {A : C}
    {f : A ⟶ (sChain X R).X n}
    (hf : FactorsThroughSmallChainInclusion R U n
      (f ≫ (genericSingSubdivIterHomULift R X k).f n)) :
    FactorsThroughSmallChainInclusion R U n
      (f ≫ (genericSingSubdivIterHomULift R X (k + d)).f n) := by
  obtain ⟨g, hg⟩ := hf
  refine ⟨g ≫ smallSubdivisionIterateLiftULift R U d n, ?_⟩
  calc
    (g ≫ smallSubdivisionIterateLiftULift R U d n) ≫
          (smallChainInclusion (C := C) R U).f n =
        g ≫ (smallSubdivisionIterateLiftULift R U d n ≫
          (smallChainInclusion (C := C) R U).f n) := Category.assoc _ _ _
    _ = g ≫ ((smallChainInclusion (C := C) R U).f n ≫
          (genericSingSubdivIterHomULift R X d).f n) := by
        rw [smallSubdivisionIterateLiftULift_comp_inclusion]
    _ = (g ≫ (smallChainInclusion (C := C) R U).f n) ≫
          (genericSingSubdivIterHomULift R X d).f n := (Category.assoc _ _ _).symm
    _ = (f ≫ (genericSingSubdivIterHomULift R X k).f n) ≫
          (genericSingSubdivIterHomULift R X d).f n := by rw [hg]
    _ = f ≫ ((genericSingSubdivIterHomULift R X k).f n ≫
          (genericSingSubdivIterHomULift R X d).f n) := Category.assoc _ _ _
    _ = f ≫ (genericSingSubdivIterHomULift R X k ≫
          genericSingSubdivIterHomULift R X d).f n := by
        rw [← HomologicalComplex.comp_f]
    _ = f ≫ (genericSingSubdivIterHomULift R X (k + d)).f n := by
        rw [← genericSingSubdivIterHomULift_add R X k d]

/-- A map from a finitely presentable object into singular chains eventually
factors through the small-chain inclusion after iterated subdivision. -/
theorem exists_iterate_morphism_factorsULift
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] [HasFiniteCoproducts C] [HasCoequalizers C]
    (R G : C) [CategoryTheory.IsFinitelyPresentable.{w} G]
    (X : TopCat.{w}) {ι : Type*} (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (Set.univ : Set X) ⊆ ⋃ i, U i)
    (n : ℕ) (x : G ⟶ (sChain X R).X n) :
    ∃ k, FactorsThroughSmallChainInclusion R U n
      (x ≫ (genericSingSubdivIterHomULift R X k).f n) := by
  classical
  let simplices := (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)
  change G ⟶ ∐ (fun _ : simplices => R) at x
  obtain ⟨S, y, hy⟩ :=
    CategoryTheory.IsFinitelyPresentable.exists_factor_through_finiteSubcoproduct
      G (fun _ : simplices => R) x
  change G ⟶ (∐ fun _ : S => R) at y
  let stop : Discrete simplices → ℕ := fun σ =>
    (exists_iterate_simplex_factorsULift R X U hUopen hUcover n σ.as).choose
  let K : ℕ := S.sup stop
  have hFactors : ∀ σ : S, FactorsThroughSmallChainInclusion R U n
      (Sigma.ι (fun _ : simplices => R) σ.1.as ≫
        (genericSingSubdivIterHomULift R X K).f n) := by
    intro σ
    have hs : stop σ.1 ≤ K := Finset.le_sup (f := stop) σ.2
    have hAdd : stop σ.1 + (K - stop σ.1) = K := Nat.add_sub_cancel' hs
    have hf_stop : FactorsThroughSmallChainInclusion R U n
        (Sigma.ι (fun _ : simplices => R) σ.1.as ≫
          (genericSingSubdivIterHomULift R X (stop σ.1)).f n) :=
      (exists_iterate_simplex_factorsULift R X U hUopen hUcover n σ.1.as).choose_spec
    have hf_plus := factors_iterate_of_factorsULift R U n
      (stop σ.1) (K - stop σ.1) hf_stop
    rw [hAdd] at hf_plus
    exact hf_plus
  let g : (∐ fun _ : S => R) ⟶
      (smallChainComplex (C := C) R U).X n :=
    Sigma.desc fun σ : S => Classical.choose (hFactors σ)
  have hLeg (σ : S) :
      Sigma.ι (fun _ : S => R) σ ≫
          (CategoryTheory.Limits.CoproductsFromFiniteFiltered.finiteSubcoproductsCocone
            (fun _ : simplices => R)).ι.app S =
        Sigma.ι (fun _ : simplices => R) σ.1.as := by
    simp [CategoryTheory.Limits.CoproductsFromFiniteFiltered.finiteSubcoproductsCocone]
  have hg : g ≫ (smallChainInclusion (C := C) R U).f n =
      (CategoryTheory.Limits.CoproductsFromFiniteFiltered.finiteSubcoproductsCocone
        (fun _ : simplices => R)).ι.app S ≫
        (genericSingSubdivIterHomULift R X K).f n := by
    apply Sigma.hom_ext
    intro σ
    calc
      Sigma.ι (fun _ : S => R) σ ≫
          (g ≫ (smallChainInclusion (C := C) R U).f n) =
        (Sigma.ι (fun _ : S => R) σ ≫ g) ≫
          (smallChainInclusion (C := C) R U).f n := (Category.assoc _ _ _).symm
      _ = Classical.choose (hFactors σ) ≫
          (smallChainInclusion (C := C) R U).f n := by rw [Sigma.ι_comp_desc]
      _ = Sigma.ι (fun _ : simplices => R) σ.1.as ≫
          (genericSingSubdivIterHomULift R X K).f n :=
        (hFactors σ).choose_spec
      _ = (Sigma.ι (fun _ : S => R) σ ≫
          (CategoryTheory.Limits.CoproductsFromFiniteFiltered.finiteSubcoproductsCocone
            (fun _ : simplices => R)).ι.app S) ≫
          (genericSingSubdivIterHomULift R X K).f n :=
        (congrArg (fun q => q ≫ (genericSingSubdivIterHomULift R X K).f n)
          (hLeg σ)).symm
      _ = Sigma.ι (fun _ : S => R) σ ≫
          ((CategoryTheory.Limits.CoproductsFromFiniteFiltered.finiteSubcoproductsCocone
            (fun _ : simplices => R)).ι.app S ≫
          (genericSingSubdivIterHomULift R X K).f n) := Category.assoc _ _ _
  refine ⟨K, ?_⟩
  refine ⟨y ≫ g, ?_⟩
  calc
    (y ≫ g) ≫ (smallChainInclusion (C := C) R U).f n =
        y ≫ (g ≫ (smallChainInclusion (C := C) R U).f n) := Category.assoc _ _ _
    _ = y ≫
        (CategoryTheory.Limits.CoproductsFromFiniteFiltered.finiteSubcoproductsCocone
          (fun _ : simplices => R)).ι.app S ≫
          (genericSingSubdivIterHomULift R X K).f n :=
      congrArg (fun q => y ≫ q) hg
    _ = (y ≫
        (CategoryTheory.Limits.CoproductsFromFiniteFiltered.finiteSubcoproductsCocone
          (fun _ : simplices => R)).ι.app S) ≫
          (genericSingSubdivIterHomULift R X K).f n := (Category.assoc _ _ _).symm
    _ = x ≫ (genericSingSubdivIterHomULift R X K).f n :=
      congrArg (fun q => q ≫ (genericSingSubdivIterHomULift R X K).f n) hy

/-- The small-chain inclusion is a quasi-isomorphism whenever the coefficient
category has a projective finitely presentable separator. -/
theorem smallChain_inclusion_quasiIsoULift
    {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (R G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (Set.univ : Set X) ⊆ ⋃ i, U i) :
    QuasiIso (smallChainInclusion (C := C) R U) := by
  apply HomologicalComplex.quasiIso_of_eventually_factors_through_projective_separator
    (smallChainInclusion (C := C) R U) G hG
    (fun k => smallSubdivisionIterateHomULift R U k)
    (fun k => genericSingSubdivIterHomULift R X k)
  · intro k n
    exact smallSubdivisionIterateHomULift_homologyMap_eq_id R U k n
  · intro k n
    rw [← (genericSingSubdivIterHomotopyULift R X k).homologyMap_eq n]
    exact HomologicalComplex.homologyMap_id (sChain X R) n
  · intro k
    exact smallSubdivisionIterateHomULift_comp_inclusion R U k
  · intro n x
    obtain ⟨k, y, hy⟩ :=
      exists_iterate_morphism_factorsULift R G X U hUopen hUcover n x
    exact ⟨k, y, hy⟩

/-- The small-chain inclusion remains a quasi-isomorphism after refining an
open cover, in an arbitrary universe. -/
theorem smallChain_inclusion_quasiIsoULift_of_open_refinement
    {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (R G : C) [Projective G] [CategoryTheory.IsFinitelyPresentable.{w} G]
    (hG : CategoryTheory.IsSeparator G)
    {X : TopCat.{w}} {ι κ : Type*}
    (U : ι → Set X) (V : κ → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (Set.univ : Set X) ⊆ ⋃ i, U i)
    (h_le : subordinateCover U ≤ subordinateCover V) :
    QuasiIso (smallChainInclusion (C := C) R V) := by
  apply HomologicalComplex.quasiIso_of_eventually_factors_through_projective_separator
    (smallChainInclusion (C := C) R V) G hG
    (fun k => smallSubdivisionIterateHomULift R V k)
    (fun k => genericSingSubdivIterHomULift R X k)
  · intro k n
    exact smallSubdivisionIterateHomULift_homologyMap_eq_id R V k n
  · intro k n
    rw [← (genericSingSubdivIterHomotopyULift R X k).homologyMap_eq n]
    exact HomologicalComplex.homologyMap_id (sChain X R) n
  · intro k
    exact smallSubdivisionIterateHomULift_comp_inclusion R V k
  · intro n x
    obtain ⟨k, y, hy⟩ :=
      exists_iterate_morphism_factorsULift R G X U hUopen hUcover n x
    refine ⟨k, y ≫ (smallChainMapOfLE R U V h_le).f n, ?_⟩
    calc
      (y ≫ (smallChainMapOfLE R U V h_le).f n) ≫
          (smallChainInclusion (C := C) R V).f n =
        y ≫ ((smallChainMapOfLE R U V h_le).f n ≫
          (smallChainInclusion (C := C) R V).f n) := Category.assoc _ _ _
      _ = y ≫ (smallChainInclusion (C := C) R U).f n := by
        rw [← HomologicalComplex.comp_f, smallChainMapOfLE_comp_inclusion]
      _ = x ≫ (genericSingSubdivIterHomULift R X k).f n := hy

/-- Compatibility forward for the moved generic Lebesgue-number corollary.

For new code, use `Metric.exists_diam_lt_subordinate_of_compact` directly. -/
@[deprecated "Use `Metric.exists_diam_lt_subordinate_of_compact` instead." (since := "2026-09-28")]
theorem exists_diam_lt_subordinate_of_compact
    {K : Type w} [PseudoMetricSpace K] [CompactSpace K]
    {X : Type*} [TopologicalSpace X]
    (g : C(K, X)) {ι : Sort*} (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (Set.univ : Set X) ⊆ ⋃ i, U i) :
    ∃ δ > 0, ∀ s : Set K,
      s.Nonempty → Metric.diam s < δ → ∃ i, g '' s ⊆ U i :=
  Metric.exists_diam_lt_subordinate_of_compact g U hUopen hUcover

/-- Compatibility forward for the moved generic geometric-decay cover theorem.

For new code, use `Metric.exists_pow_mul_diam_subordinate_of_compact` directly. -/
@[deprecated "Use `Metric.exists_pow_mul_diam_subordinate_of_compact` instead."
  (since := "2026-09-28")]
theorem exists_iterate_diam_subordinate_of_compact
    (n : ℕ)
    {K : Type w} [PseudoMetricSpace K] [CompactSpace K]
    {X : Type*} [TopologicalSpace X]
    (g : C(K, X)) {ι : Sort*} (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : (Set.univ : Set X) ⊆ ⋃ i, U i) :
    ∃ k : ℕ, ∀ s : Set K,
      s.Nonempty →
      Metric.diam s ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ k *
        Metric.diam (Set.univ : Set K) →
      ∃ i, g '' s ⊆ U i := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hq0 : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) :=
    div_nonneg (Nat.cast_nonneg _) hpos.le
  have hq1 : (n : ℝ) / ((n : ℝ) + 1) < 1 :=
    (div_lt_one hpos).mpr (lt_add_of_pos_right _ one_pos)
  exact Metric.exists_pow_mul_diam_subordinate_of_compact _ _ hq0 hq1
    Metric.diam_nonneg g U hUopen hUcover

end AlgebraicTopology
