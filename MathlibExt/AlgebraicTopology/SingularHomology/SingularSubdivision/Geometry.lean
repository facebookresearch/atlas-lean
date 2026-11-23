/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.LinearSubdivision.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import MathlibExt.AlgebraicTopology.SingularSet.Simplex

/-!
# Singular subdivision geometry

Chain support, subdivision support, iterated subdivision, affine realization,
standard affine simplex, and coface-membership foundations for barycentric
subdivision. Chain-valued results are generic over a preadditive target.
-/

@[expose] public section

open scoped BigOperators
open CategoryTheory Simplicial SimplexCategory SimplicialObject Matrix Limits Opposite

namespace AlgebraicTopology

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
variable {R : C} {V W : Type w}

section ChainSupportGeneric

variable {V : Type w}

noncomputable def chainSpan (R : C) (n : ℕ) (X : Set (Fin (n + 1) → V)) :
    AddSubgroup (R ⟶ (freemod (C := C) R V).obj (Opposite.op ⦋n⦌)) :=
  AddSubgroup.closure ((fun τ => Sigma.ι (fun _ : (Fin (n + 1) → V) => (R : C)) τ) '' X)

lemma sigma_ι_mem_chainSpan {R : C} {n : ℕ} {X : Set (Fin (n + 1) → V)}
    {τ : Fin (n + 1) → V} (h : τ ∈ X) :
    Sigma.ι (fun _ : (Fin (n + 1) → V) => (R : C)) τ ∈ chainSpan (C := C) R n X :=
  AddSubgroup.subset_closure ⟨τ, h, rfl⟩

lemma chainSpan_mono {R : C} {n : ℕ} {X Y : Set (Fin (n + 1) → V)} (h : X ⊆ Y) :
    chainSpan (C := C) R n X ≤ chainSpan (C := C) R n Y :=
  AddSubgroup.closure_mono (Set.image_mono h)

lemma chainSpan_comp_aux {R : C} {n m : ℕ} {X : Set (Fin (n + 1) → V)}
    {Y : Set (Fin (m + 1) → V)}
    {f : (freemod (C := C) R V).obj (Opposite.op ⦋n⦌) ⟶
      (freemod (C := C) R V).obj (Opposite.op ⦋m⦌)}
    (hf : ∀ τ ∈ X,
      Sigma.ι (fun _ : (Fin (n + 1) → V) => (R : C)) τ ≫ f ∈
        chainSpan (C := C) R m Y)
    {c : R ⟶ (freemod (C := C) R V).obj (Opposite.op ⦋n⦌)}
    (hc : c ∈ chainSpan (C := C) R n X) :
    c ≫ f ∈ chainSpan (C := C) R m Y := by
  have hle : chainSpan (C := C) R n X ≤ (chainSpan (C := C) R m Y).comap
      (AddMonoidHom.mk' (fun g => g ≫ f) (by intro a b; simp [Preadditive.add_comp])) := by
    rw [chainSpan, AddSubgroup.closure_le]
    rintro _ ⟨τ, hτ, rfl⟩
    exact hf τ hτ
  exact hle hc

def facesOf {k : ℕ} (X : Set (Fin (k + 2) → V)) : Set (Fin (k + 1) → V) :=
  {ρ | ∃ τ ∈ X, ∃ i : Fin (k + 2), ρ = τ ∘ Fin.succAbove i}

lemma coneMap_chainSpan {R : C} {k : ℕ} {X : Set (Fin (k + 1) → V)} (b : V)
    {c : R ⟶ (freemod (C := C) R V).obj (Opposite.op ⦋k⦌)} (hc : c ∈ chainSpan (C := C) R k X) :
    c ≫ coneMap (C := C) R V b k ∈ chainSpan (C := C) R (k + 1) (Matrix.vecCons b '' X) := by
  refine chainSpan_comp_aux (fun τ hτ => ?_) hc
  change SSet.ιChainComplex (X := linSSet (Y := V)) (R := R) τ ≫ coneMap (C := C) R V b k ∈ _
  have heq : SSet.ιChainComplex (X := linSSet (Y := V)) (R := R) τ ≫ coneMap (C := C) R V b k =
      SSet.ιChainComplex (X := linSSet (Y := V)) (R := R) (Matrix.vecCons b τ) :=
    sigma_ι_comp_coneMap (C := C) b τ
  rw [heq]
  exact sigma_ι_mem_chainSpan ⟨τ, hτ, rfl⟩

@[reassoc]
private lemma linSSet_ιChainComplex_eq_sigma_ι
    {R : C} {V : Type w} {k : ℕ}
    (τ : (linSSet V).obj (Opposite.op ⦋k + 1⦌)) :
    SSet.ιChainComplex (X := linSSet V) (R := R) τ =
      Sigma.ι (fun _ : (Fin (k + 2) → V) => (R : C))
        (show Fin (k + 2) → V from τ) := by
  rfl

@[reassoc]
private lemma sigma_ι_comp_freeBoundary {R : C} {V : Type w} {k : ℕ}
    (τ : Fin (k + 2) → V) :
    Sigma.ι (fun _ : (Fin (k + 2) → V) => (R : C)) τ ≫
        freeBoundary (C := C) R V k =
      ∑ i : Fin (k + 2),
        (-1 : ℤ) ^ (i : ℕ) • Sigma.ι (fun _ : (Fin (k + 1) → V) => (R : C))
          (τ ∘ Fin.succAbove i) := by
  rw [freeBoundary_eq_d (C := C)]
  erw [linearChainComplex_d (C := C)]
  erw [Preadditive.comp_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  erw [Preadditive.comp_zsmul, sigma_ι_comp_freemod_δ (C := C)]
  rfl

lemma freeBoundary_chainSpan {R : C} {k : ℕ} {X : Set (Fin (k + 2) → V)}
    {c : R ⟶ (freemod (C := C) R V).obj (Opposite.op ⦋k + 1⦌)}
    (hc : c ∈ chainSpan (C := C) R (k + 1) X) :
    c ≫ freeBoundary (C := C) R V k ∈ chainSpan (C := C) R k (facesOf X) := by
  refine chainSpan_comp_aux (fun τ hτ => ?_) hc
  rw [sigma_ι_comp_freeBoundary (C := C)]
  refine sum_mem (fun i _ => zsmul_mem ?_ _)
  exact sigma_ι_mem_chainSpan ⟨τ, hτ, i, rfl⟩

end ChainSupportGeneric

section SubdivSupport

variable {W : Type w} [NormedAddCommGroup W] [NormedSpace ℝ W]

def subdivSimplices {n : ℕ} (σ : Fin (n + 1) → W) : Set (Fin (n + 1) → W) :=
  {τ | Set.range τ ⊆ convexHull ℝ (Set.range σ)
    ∧ Metric.diam (Set.range τ) ≤ ((n : ℝ) / ((n : ℝ) + 1)) * Metric.diam (Set.range σ)}

theorem subdivision_mem_chainSpan (R : C) (n : ℕ) (σ : Fin (n + 1) → W) :
    Sigma.ι (fun _ : (Fin (n + 1) → W) => (R : C)) σ ≫ subdivision (C := C) R W n
      ∈ chainSpan (C := C) R n (subdivSimplices σ) := by
  induction n with
  | zero =>
    rw [subdivision_zero (C := C)]
    erw [Category.comp_id]
    have hrange : Set.Subsingleton (Set.range σ) := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      congr
      exact (Fin.eq_zero i).trans (Fin.eq_zero j).symm
    refine sigma_ι_mem_chainSpan ⟨subset_convexHull ℝ _, ?_⟩
    have hsub : Metric.diam (Set.range σ) = 0 :=
      Metric.diam_subsingleton hrange
    simp [hsub]
  | succ m ih =>
    rw [subdivision_succ' (C := C)]
    erw [Sigma.ι_comp_desc]
    erw [← Category.assoc, ← Category.assoc]
    have hc : (Sigma.ι (fun _ : (Fin (m + 2) → W) => (R : C)) σ ≫
          freeBoundary (C := C) R W m) ≫
        subdivision (C := C) R W m ∈
        chainSpan (C := C) R m
          {ρ | ∃ τ ∈ facesOf ({σ} : Set (Fin (m + 2) → W)),
            ρ ∈ subdivSimplices τ} := by
      apply chainSpan_comp_aux _
        (freeBoundary_chainSpan
          (sigma_ι_mem_chainSpan
            (X := ({σ} : Set (Fin (m + 2) → W))) rfl))
      intro τ hτ
      refine chainSpan_mono (fun ρ hρ => ?_) (ih τ)
      exact ⟨τ, hτ, hρ⟩
    refine chainSpan_mono ?_ (coneMap_chainSpan (C := C) (linSimplexBarycenter σ) hc)
    rintro _ ⟨w, hwZ, rfl⟩
    obtain ⟨τ, hτ, hwsub, hwdiam⟩ := hwZ
    obtain ⟨σ', hσ'mem, i, rfl⟩ := hτ
    rw [Set.mem_singleton_iff] at hσ'mem
    subst σ'
    have hσbd : Bornology.IsBounded (Set.range σ) := (Set.finite_range σ).isBounded
    have hdiam0 : 0 ≤ Metric.diam (Set.range σ) := Metric.diam_nonneg
    have hface : Set.range (σ ∘ Fin.succAbove i) ⊆ Set.range σ := Set.range_comp_subset_range _ _
    have hfacediam : Metric.diam (Set.range (σ ∘ Fin.succAbove i)) ≤ Metric.diam (Set.range σ) :=
      Metric.diam_mono hface hσbd
    have hwhull : Set.range w ⊆ convexHull ℝ (Set.range σ) := hwsub.trans (convexHull_mono hface)
    have hfrac : ((m : ℝ) / ((m : ℝ) + 1)) ≤ ((m : ℝ) + 1) / ((m : ℝ) + 1 + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨j, rfl⟩ := hx
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa using linSimplexBarycenter_mem_convexHull σ
      · simpa using hwhull (Set.mem_range_self k)
    · push_cast
      refine diam_vecCons_le _ w (by positivity) ?_ (fun j => ?_)
      · refine hwdiam.trans ?_
        calc (m : ℝ) / ((m : ℝ) + 1) * Metric.diam (Set.range (σ ∘ Fin.succAbove i))
            ≤ (m : ℝ) / ((m : ℝ) + 1) * Metric.diam (Set.range σ) := by
              apply mul_le_mul_of_nonneg_left hfacediam; positivity
          _ ≤ ((m : ℝ) + 1) / ((m : ℝ) + 1 + 1) * Metric.diam (Set.range σ) := by
              apply mul_le_mul_of_nonneg_right hfrac hdiam0
      · have hd := dist_linSimplexBarycenter_le_of_mem σ (hwhull (Set.mem_range_self j))
        push_cast at hd
        simp only [dist_eq_norm] at hd ⊢
        exact hd

def hullSimplices {V : Type w} [AddCommGroup V] [Module ℝ V] {n m : ℕ} (σ : Fin (n + 1) → V) :
    Set (Fin (m + 1) → V) := {τ | Set.range τ ⊆ convexHull ℝ (Set.range σ)}

lemma vecCons_mem_hullSimplices {V : Type w} [AddCommGroup V] [Module ℝ V] {n m : ℕ}
    {σ : Fin (n + 1) → V} {b : V} {v : Fin (m + 1) → V}
    (hb : b ∈ convexHull ℝ (Set.range σ)) (hv : Set.range v ⊆ convexHull ℝ (Set.range σ)) :
    Matrix.vecCons b v ∈ hullSimplices (m := m + 1) σ := by
  intro x hx; obtain ⟨j, rfl⟩ := hx; exact Fin.cases hb (fun k => hv (Set.mem_range_self k)) j

theorem homotopyOp_mem_chainSpan (R : C) (n : ℕ) (σ : Fin (n + 1) → W) :
    Sigma.ι (fun _ : (Fin (n + 1) → W) => (R : C)) σ ≫ homotopyOp (C := C) R W n
      ∈ chainSpan (C := C) R (n + 1) (hullSimplices (m := n + 1) σ) := by
  induction n with
  | zero =>
    rw [homotopyOp_zero (C := C), Sigma.ι_comp_desc]
    refine chainSpan_mono ?_ (coneMap_chainSpan (C := C) (linSimplexBarycenter σ)
      (X := hullSimplices (m := 0) σ) ?_)
    · rintro _ ⟨w, hw, rfl⟩
      exact vecCons_mem_hullSimplices (linSimplexBarycenter_mem_convexHull σ) hw
    · exact sigma_ι_mem_chainSpan (subset_convexHull ℝ _)
  | succ m ih =>
    rw [homotopyOp_succ' (C := C), Sigma.ι_comp_desc, ← Category.assoc]
    refine chainSpan_mono ?_ (coneMap_chainSpan (C := C) (linSimplexBarycenter σ)
      (X := hullSimplices (m := m + 1) σ) ?_)
    · rintro _ ⟨w, hw, rfl⟩
      exact vecCons_mem_hullSimplices (linSimplexBarycenter_mem_convexHull σ) hw
    · erw [Preadditive.comp_sub, Category.comp_id]
      refine sub_mem ?_ ?_
      · exact sigma_ι_mem_chainSpan (subset_convexHull ℝ _)
      · erw [← Category.assoc]
        refine chainSpan_comp_aux (fun τ hτ => ?_) (freeBoundary_chainSpan
          (sigma_ι_mem_chainSpan (X := ({σ} : Set (Fin (m + 2) → W))) rfl))
        obtain ⟨τ₀, hτ₀, i, rfl⟩ := hτ
        rw [Set.mem_singleton_iff] at hτ₀; subst τ₀
        refine chainSpan_mono (fun ρ hρ => ?_) (ih (σ ∘ Fin.succAbove i))
        exact hρ.trans (convexHull_mono (Set.range_comp_subset_range _ _))

noncomputable def subdivIter (R : C) (n k : ℕ) :
    (freemod (C := C) R W).obj (Opposite.op ⦋n⦌) ⟶
      (freemod (C := C) R W).obj (Opposite.op ⦋n⦌) := by
  induction k with
  | zero => exact 𝟙 _
  | succ _ ih => exact subdivision (C := C) R W n ≫ ih

@[simp] lemma subdivIter_zero (R : C) (n : ℕ) : subdivIter (C := C) (W := W) R n 0 = 𝟙 _ := rfl

lemma subdivIter_succ (R : C) (n k : ℕ) :
    subdivIter (C := C) (W := W) R n (k + 1) =
      subdivision (C := C) R W n ≫ subdivIter (C := C) R n k :=
  rfl

def subdivIterSimplices {n : ℕ} (k : ℕ) (σ : Fin (n + 1) → W) : Set (Fin (n + 1) → W) :=
  {τ | Set.range τ ⊆ convexHull ℝ (Set.range σ)
    ∧ Metric.diam (Set.range τ) ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ k * Metric.diam (Set.range σ)}

theorem subdivIter_mem_chainSpan (R : C) (n k : ℕ) (σ : Fin (n + 1) → W) :
    Sigma.ι (fun _ : (Fin (n + 1) → W) => (R : C)) σ ≫ subdivIter (C := C) R n k
      ∈ chainSpan (C := C) R n (subdivIterSimplices k σ) := by
  induction k generalizing σ with
  | zero =>
    rw [subdivIter_zero (C := C)]
    erw [Category.comp_id]
    exact sigma_ι_mem_chainSpan ⟨subset_convexHull ℝ _, by rw [pow_zero, one_mul]⟩
  | succ j ih =>
    rw [subdivIter_succ (C := C)]
    erw [← Category.assoc]
    refine chainSpan_comp_aux (fun τ hτ => ?_) (subdivision_mem_chainSpan (C := C) R n σ)
    obtain ⟨hτsub, hτdiam⟩ := hτ
    refine chainSpan_mono (fun ρ hρ => ?_) (ih τ)
    obtain ⟨hρsub, hρdiam⟩ := hρ
    have hhull : convexHull ℝ (Set.range τ) ⊆ convexHull ℝ (Set.range σ) :=
      (convexHull_mono hτsub).trans_eq (convexHull_eq_self.mpr (convex_convexHull ℝ _))
    refine ⟨hρsub.trans hhull, ?_⟩
    calc Metric.diam (Set.range ρ)
        ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ j * Metric.diam (Set.range τ) := hρdiam
      _ ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ j * (((n : ℝ) / ((n : ℝ) + 1)) * Metric.diam (Set.range σ)) :=
          mul_le_mul_of_nonneg_left hτdiam (by positivity)
      _ = ((n : ℝ) / ((n : ℝ) + 1)) ^ (j + 1) * Metric.diam (Set.range σ) := by rw [pow_succ]; ring

end SubdivSupport

section AffineRealization

variable {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def affineRealize {n : ℕ} (σ : Fin (n + 1) → V) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), V) :=
  ⟨fun w => ∑ i, w.weights i • σ i,
    continuous_finsetSum _ fun i _ =>
      (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i).smul
        continuous_const⟩

@[simp] lemma affineRealize_apply {n : ℕ} (σ : Fin (n + 1) → V)
    (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    affineRealize σ w = ∑ i, w.weights i • σ i := rfl

lemma affineRealize_mem_convexHull {n : ℕ} (σ : Fin (n + 1) → V)
    (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    affineRealize σ w ∈ convexHull ℝ (Set.range σ) := by
  rw [affineRealize_apply]
  have hx_nonneg : ∀ i, 0 ≤ w.weights i := fun i => w.weights_nonneg i
  have hx_sum : ∑ i, w.weights i = 1 := w.total_of_fintype
  refine (convex_convexHull ℝ (Set.range σ)).sum_mem (fun i _ => hx_nonneg i) hx_sum
    (fun i _ => subset_convexHull ℝ _ (Set.mem_range_self i))

lemma affineRealize_comp_map {k m : ℕ} (σ : Fin (k + 1) → V)
    (φ : Fin (m + 1) → Fin (k + 1)) :
    affineRealize (σ ∘ φ) =
      (affineRealize σ).comp
        ⟨Convexity.StdSimplex.map φ,
          Convexity.StdSimplex.continuous_map (R := ℝ) φ⟩ := by
  ext w
  simp only [affineRealize_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, Function.comp_apply]
  have h_weights : ∀ j : Fin (k + 1),
      (Convexity.StdSimplex.map φ w).weights j =
        ∑ i ∈ Finset.univ.filter (fun i => φ i = j), w.weights i := by
    intro j
    have h1 : (Convexity.StdSimplex.map φ w).weights =
        Finsupp.mapDomain φ w.weights := rfl
    rw [h1, Finsupp.mapDomain_fintype]
    rw [Finsupp.finsetSum_apply]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : φ i = j
    · simp [h]
    · simp [h]
  have h : ∑ i : Fin (m + 1), w.weights i • σ (φ i) =
      ∑ j : Fin (k + 1),
        (∑ i ∈ Finset.univ.filter (fun i => φ i = j), w.weights i) • σ j := by
    rw [← Finset.sum_fiberwise Finset.univ φ (fun i => w.weights i • σ (φ i))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_filter] at hi
    rw [hi.2]
  rw [h]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [h_weights j]

end AffineRealization

section LinSSetIn

def linSSetIn (V : Type w) (K : Set V) : SSet.{w} where
  obj m := { σ : Fin (m.unop.len + 1) → V // ∀ i, σ i ∈ K }
  map f :=
    TypeCat.ofHom
      (fun ⟨a, h⟩ => ⟨a ∘ Hom.toOrderHom f.unop, fun _ => h _⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

def linSSetInForget (V : Type w) (K : Set V) :
    linSSetIn V K ⟶ AlgebraicTopology.linSSet V where
  app _ :=
    TypeCat.ofHom fun ⟨a, _⟩ => a
  naturality _ _ _ := rfl

end LinSSetIn

section ChainBridge

open scoped Classical in
noncomputable def liftIn (R : C) (K : Set V) (n : ℕ) :
    ((linSSet V).chainComplex R).X n ⟶ ((linSSetIn V K).chainComplex R).X n :=
  Sigma.desc fun τ =>
    if h : ∀ i, τ i ∈ K then
      SSet.ιChainComplex (X := linSSetIn V K) (R := R) ⟨τ, h⟩
    else 0

noncomputable def forgetChain (R : C) (K : Set V) :
    (linSSetIn V K).chainComplex R ⟶ (linSSet V).chainComplex R :=
  SSet.chainComplexMap (linSSetInForget V K) R

@[reassoc]
lemma forgetChain_ι (R : C) (K : Set V) (n : ℕ)
    (σ : (linSSetIn V K).obj (Opposite.op ⦋n⦌)) :
    SSet.ιChainComplex (X := linSSetIn V K) (R := R) σ ≫
      (forgetChain R K).f n =
      SSet.ιChainComplex (X := linSSet V) (R := R) σ.1 := by
  unfold forgetChain
  rw [SSet.ι_chainComplexMap_f]
  rfl

open scoped Classical in
@[reassoc]
lemma liftIn_ι (R : C) (K : Set V) (n : ℕ) (τ : Fin (n + 1) → V) :
    SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫ liftIn R K n =
      if h : ∀ i, τ i ∈ K then
        SSet.ιChainComplex (X := linSSetIn V K) (R := R) ⟨τ, h⟩
      else 0 := by
  unfold liftIn
  change
    Sigma.ι (fun _ : Fin (n + 1) → V => (R : C)) τ ≫
        Sigma.desc (fun τ : Fin (n + 1) → V =>
          if h : ∀ i, τ i ∈ K then
            SSet.ιChainComplex (X := linSSetIn V K) (R := R) ⟨τ, h⟩
          else 0) =
      if h : ∀ i, τ i ∈ K then
        SSet.ιChainComplex (X := linSSetIn V K) (R := R) ⟨τ, h⟩
      else 0
  rw [Sigma.ι_comp_desc]

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma liftIn_naturality_coefficient
    {R S : C} (a : R ⟶ S) (V : Type w) (K : Set V) (n : ℕ) :
    liftIn (C := C) R K n ≫
        (((SSet.chainComplexFunctor C).map a).app (linSSetIn V K)).f n =
      (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f n ≫
        liftIn (C := C) S K n := by
  apply SSet.chainComplex_hom_ext
  intro τ
  by_cases h : ∀ i, τ i ∈ K
  · have hR :
        SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫ liftIn (C := C) R K n =
          SSet.ιChainComplex (X := linSSetIn V K) (R := R)
            (⟨τ, h⟩ : (linSSetIn V K).obj (Opposite.op ⦋n⦌)) := by
        rw [liftIn_ι (C := C) (R := R) (K := K) (n := n) (τ := τ),
          dite_eq_left h]
    have hS :
        SSet.ιChainComplex (X := linSSet V) (R := S) τ ≫ liftIn (C := C) S K n =
          SSet.ιChainComplex (X := linSSetIn V K) (R := S)
            (⟨τ, h⟩ : (linSSetIn V K).obj (Opposite.op ⦋n⦌)) := by
        rw [liftIn_ι (C := C) (R := S) (K := K) (n := n) (τ := τ),
          dite_eq_left h]
    calc SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫
            (liftIn (C := C) R K n ≫ (((SSet.chainComplexFunctor C).map a).app (linSSetIn V K)).f n)
        = (SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫ liftIn (C := C) R K n) ≫
            (((SSet.chainComplexFunctor C).map a).app (linSSetIn V K)).f n := by
          rw [Category.assoc]
      _ = SSet.ιChainComplex (X := linSSetIn V K) (R := R)
            (⟨τ, h⟩ : (linSSetIn V K).obj (Opposite.op ⦋n⦌)) ≫
            (((SSet.chainComplexFunctor C).map a).app (linSSetIn V K)).f n := by
        rw [hR]
      _ = a ≫ SSet.ιChainComplex (X := linSSetIn V K) (R := S)
          (⟨τ, h⟩ : (linSSetIn V K).obj (Opposite.op ⦋n⦌)) := by
          exact SSet.ιChainComplex_coefficientMap_f (a := a)
            (X := linSSetIn V K) (n := n)
            (x := (⟨τ, h⟩ : (linSSetIn V K).obj (Opposite.op ⦋n⦌)))
      _ = a ≫ (SSet.ιChainComplex (X := linSSet V) (R := S) τ ≫
          liftIn (C := C) S K n) := by rw [← hS]
      _ = (SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫
            (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f n) ≫
            liftIn (C := C) S K n := by
          rw [SSet.ιChainComplex_coefficientMap_f (a := a)
            (X := linSSet V) (n := n) (x := τ)]
          simp only [Category.assoc]
      _ = SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫
            ((((SSet.chainComplexFunctor C).map a).app (linSSet V)).f n ≫
              liftIn (C := C) S K n) := by
          rw [Category.assoc]
  · have hR : SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫
        liftIn (C := C) R K n = 0 := by
        rw [liftIn_ι (C := C) (R := R) (K := K) (n := n) (τ := τ), dite_eq_right h]
    have hS : SSet.ιChainComplex (X := linSSet V) (R := S) τ ≫ liftIn (C := C) S K n = 0 := by
        rw [liftIn_ι (C := C) (R := S) (K := K) (n := n) (τ := τ), dite_eq_right h]
    calc SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫
            (liftIn (C := C) R K n ≫ (((SSet.chainComplexFunctor C).map a).app (linSSetIn V K)).f n)
        = (SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫ liftIn (C := C) R K n) ≫
            (((SSet.chainComplexFunctor C).map a).app (linSSetIn V K)).f n := by rw [Category.assoc]
      _ = (0 : R ⟶ _) ≫ (((SSet.chainComplexFunctor C).map a).app (linSSetIn V K)).f n := by rw [hR]
      _ = 0 := by simp
      _ = a ≫ (0 : S ⟶ _) := by simp
      _ = a ≫ (SSet.ιChainComplex (X := linSSet V) (R := S) τ ≫ liftIn (C := C) S K n) := by rw [hS]
      _ = (SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫
            (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f n) ≫
            liftIn (C := C) S K n := by
          rw [SSet.ιChainComplex_coefficientMap_f (a := a)
            (X := linSSet V) (n := n) (x := τ)]
          simp only [Category.assoc]
      _ = SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫
            ((((SSet.chainComplexFunctor C).map a).app (linSSet V)).f n ≫
              liftIn (C := C) S K n) := by rw [Category.assoc]

open scoped Classical in
lemma forgetChain_f_comp_liftIn (R : C) (K : Set V) (n : ℕ) :
    (forgetChain R K).f n ≫ liftIn R K n = 𝟙 _ := by
  apply Sigma.hom_ext
  intro σ
  change
    SSet.ιChainComplex (X := linSSetIn V K) (R := R) σ ≫
        (forgetChain R K).f n ≫ liftIn R K n =
      SSet.ιChainComplex (X := linSSetIn V K) (R := R) σ ≫ 𝟙 _
  rw [forgetChain_ι_assoc]
  rw [liftIn_ι]
  rw [dite_eq_left σ.2]
  simp
  cases σ
  rfl

lemma liftIn_forgetChain_eq_self {n : ℕ}
    {X : Set (Fin (n + 1) → V)} (K : Set V)
    (hX : ∀ τ ∈ X, ∀ i, τ i ∈ K)
    {c : R ⟶ (freemod (C := C) R V).obj (Opposite.op ⦋n⦌)}
    (hc : c ∈ chainSpan (C := C) R n X) :
    c ≫ liftIn R K n ≫ (forgetChain R K).f n = c := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
      obtain ⟨τ, hτ, rfl⟩ := hx
      erw [liftIn_ι_assoc, dite_eq_left (hX τ hτ), forgetChain_ι]
      rfl
  | zero => simp; rfl
  | add x y _ _ ihx ihy => simp [ihx, ihy]; rfl
  | neg x _ ihx => simp [ihx]; rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma liftIn_comm_d {n : ℕ}
    {X : Set (Fin (n + 2) → V)} (K : Set V)
    (hX : ∀ τ ∈ X, ∀ i, τ i ∈ K)
    {c : R ⟶ (freemod (C := C) R V).obj (Opposite.op ⦋n + 1⦌)}
    (hc : c ∈ chainSpan (C := C) R (n + 1) X) :
    c ≫ liftIn R K (n + 1) ≫
        ((linSSetIn V K).chainComplex R).d (n + 1) n =
      c ≫ (linearChainComplex (C := C) R V).d (n + 1) n ≫ liftIn R K n := by
  have hB : c ≫ liftIn R K (n + 1) ≫ (forgetChain R K).f (n + 1) = c :=
    liftIn_forgetChain_eq_self (C := C) (R := R) (X := X) K hX hc
  have hC := (forgetChain R K).comm (n + 1) n
  have hA : (forgetChain R K).f n ≫ liftIn R K n = 𝟙 _ :=
    forgetChain_f_comp_liftIn R K n
  have hR :
      c ≫ (linearChainComplex (C := C) R V).d (n + 1) n ≫ liftIn R K n =
        c ≫ liftIn R K (n + 1) ≫
          ((linSSetIn V K).chainComplex R).d (n + 1) n := by
    have h_expand : c = c ≫ liftIn R K (n + 1) ≫
        (forgetChain R K).f (n + 1) := hB.symm
    calc
      c ≫ (linearChainComplex (C := C) R V).d (n + 1) n ≫ liftIn R K n =
          (c ≫ liftIn R K (n + 1) ≫ (forgetChain R K).f (n + 1)) ≫
            (linearChainComplex (C := C) R V).d (n + 1) n ≫
              liftIn R K n := by
        conv_lhs => rw [h_expand]
      _ = c ≫ liftIn R K (n + 1) ≫
          ((forgetChain R K).f (n + 1) ≫
            (linearChainComplex (C := C) R V).d (n + 1) n) ≫
              liftIn R K n := by
        simp only [Category.assoc]
      _ = c ≫ liftIn R K (n + 1) ≫
          (((linSSetIn V K).chainComplex R).d (n + 1) n ≫
            (forgetChain R K).f n) ≫ liftIn R K n := by
        exact congrArg (fun t => c ≫ liftIn R K (n + 1) ≫ t ≫
          liftIn R K n) hC
      _ = c ≫ liftIn R K (n + 1) ≫
          ((linSSetIn V K).chainComplex R).d (n + 1) n ≫
            ((forgetChain R K).f n ≫ liftIn R K n) := by
        simp only [Category.assoc]
      _ = c ≫ liftIn R K (n + 1) ≫
          ((linSSetIn V K).chainComplex R).d (n + 1) n := by
        rw [hA, Category.comp_id]
  exact hR.symm

end ChainBridge

section AffineRealizeIn

variable {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def affineRealizeIn {n : ℕ} (K : Set V)
    (hK : Convex ℝ K) (σ : Fin (n + 1) → V)
    (hσ : ∀ i, σ i ∈ K) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), ↥K) where
  toFun w :=
    ⟨affineRealize σ w,
      convexHull_min (Set.range_subset_iff.mpr hσ) hK
        (affineRealize_mem_convexHull σ w)⟩
  continuous_toFun := by
    have hcont := (affineRealize (V := V) σ).continuous
    exact Continuous.subtype_mk hcont _

lemma affineRealizeIn_comp_map {k m : ℕ} (K : Set V)
    (hK : Convex ℝ K) (σ : Fin (k + 1) → V)
    (hσ : ∀ i, σ i ∈ K) (φ : Fin (m + 1) → Fin (k + 1)) :
    affineRealizeIn K hK (σ ∘ φ) (fun i => hσ (φ i)) =
      (affineRealizeIn K hK σ hσ).comp
        ⟨Convexity.StdSimplex.map φ,
          Convexity.StdSimplex.continuous_map (R := ℝ) φ⟩ := by
  ext w
  change affineRealize (σ ∘ φ) w =
      affineRealize σ (Convexity.StdSimplex.map φ w)
  have h := affineRealize_comp_map (V := V) σ φ
  have hx : (affineRealize (σ ∘ φ)) w =
      ((affineRealize σ).comp
        ⟨Convexity.StdSimplex.map φ,
          Convexity.StdSimplex.continuous_map (R := ℝ) φ⟩) w := by
    rw [h]
  simpa [ContinuousMap.comp_apply] using hx

noncomputable def realizeInNatTrans (K : Set V)
    (hK : Convex ℝ K) :
    linSSetIn V K ⟶ TopCat.toSSet.obj (TopCat.of ↥K) where
  app n :=
    TypeCat.ofHom
      (fun σ : (linSSetIn V K).obj n =>
        ((TopCat.of (↥K : Type w)).toSSetObjEquiv n).symm
          (affineRealizeIn (V := V) K hK σ.val σ.prop))
  naturality n m f := by
    ext σ
    obtain ⟨σ, hσ⟩ := σ
    dsimp [linSSetIn]
    have h1 : affineRealizeIn (V := V) K hK
        (σ ∘ Hom.toOrderHom f.unop)
        (fun i => hσ _) =
        (affineRealizeIn (V := V) K hK σ hσ).comp
          ⟨Convexity.StdSimplex.map (Hom.toOrderHom f.unop),
            Convexity.StdSimplex.continuous_map (R := ℝ) _⟩ :=
      affineRealizeIn_comp_map K hK σ hσ _
    rw [h1]
    exact (TopCat.toSSetObjEquiv_symm_naturality
      (X := TopCat.of (↥K : Type w))
      (f := f.unop)
      (g := affineRealizeIn K hK σ hσ)).symm

noncomputable def realizeInChain (R : C) (K : Set V)
    (hK : Convex ℝ K) :
    (linSSetIn V K).chainComplex R ⟶
      (TopCat.toSSet.obj (TopCat.of ↥K)).chainComplex R :=
  SSet.chainComplexMap (realizeInNatTrans (V := V) K hK) R

@[reassoc]
lemma realizeInChain_ι (R : C) (K : Set V)
    (hK : Convex ℝ K) (n : ℕ)
    (σ : (linSSetIn V K).obj (Opposite.op ⦋n⦌)) :
    SSet.ιChainComplex (X := linSSetIn V K) (R := R) σ ≫
        (realizeInChain (C := C) R K hK).f n =
      SSet.ιChainComplex
        (X := TopCat.toSSet.obj (TopCat.of ↥K)) (R := R)
        ((realizeInNatTrans (V := V) K hK).app
          (Opposite.op ⦋n⦌) σ) := by
  unfold realizeInChain
  rw [SSet.ι_chainComplexMap_f]

@[reassoc]
lemma realizeInChain_naturality_coefficient
    {R S : C} (a : R ⟶ S) (V : Type w) (K : Set V)
    [NormedAddCommGroup V] [NormedSpace ℝ V] (hK : Convex ℝ K) :
    realizeInChain (C := C) R K hK ≫
        (((SSet.chainComplexFunctor C).map a).app
          (TopCat.toSSet.obj (TopCat.of ↑K))) =
      (((SSet.chainComplexFunctor C).map a).app
          (linSSetIn V K)) ≫
        realizeInChain (C := C) S K hK := by
  have h := ((SSet.chainComplexFunctor C).map a).naturality (realizeInNatTrans (V := V) K hK)
  simp only [realizeInChain] at h ⊢
  exact h

end AffineRealizeIn

noncomputable def simplexLinMap {n k : ℕ}
    (τ : Fin (k + 1) → (Fin (n + 1) → ℝ)) :
    (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun x := ∑ i, x i • τ i
  map_add' x y := by simp [Finset.sum_add_distrib, add_smul]
  map_smul' r x := by simp [Finset.smul_sum, smul_smul]

lemma simplexLinMap_apply {n k : ℕ}
    (τ : Fin (k + 1) → (Fin (n + 1) → ℝ)) (x : Fin (k + 1) → ℝ) :
    simplexLinMap τ x = ∑ i, x i • τ i := rfl

section RealizeAux

variable {V W : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma affineRealize_comp_linear (L : V →ₗ[ℝ] W) {d : ℕ}
    (σ : Fin (d + 1) → V) (w : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    affineRealize (L ∘ σ) w = L (affineRealize σ w) := by
  simp only [affineRealize_apply, Function.comp_apply, map_sum, map_smul]

end RealizeAux

section LiftedStdSimplex

/-- ULifted range of the new weights embedding. -/
def liftedStdSimplex (n : ℕ) :
    Set (ULift.{w} (Fin (n + 1) → ℝ)) :=
  Set.range (fun w : Convexity.StdSimplex ℝ (Fin (n + 1)) => ULift.up (⇑w.weights))

private lemma convex_range_weights (n : ℕ) :
    Convex ℝ (Set.range
      (fun w : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
        (⇑w.weights : Fin (n + 1) → ℝ))) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨aw, rfl⟩ := hx
  obtain ⟨bw, rfl⟩ := hy
  refine ⟨Convexity.convexCombPair a b ha hb hab aw bw, ?_⟩
  have hweights : (Convexity.convexCombPair a b ha hb hab aw bw).weights =
      a • aw.weights + b • bw.weights :=
    Convexity.StdSimplex.weights_convexCombPair aw bw a b ha hb hab
  have hcoe : (⇑(Convexity.convexCombPair a b ha hb hab aw bw).weights :
      Fin (n + 1) → ℝ) = a • ⇑aw.weights + b • ⇑bw.weights := by
    rw [hweights]
    simp [Finsupp.coe_add, Finsupp.coe_smul]
  exact hcoe

lemma convex_liftedStdSimplex (n : ℕ) :
    Convex ℝ (liftedStdSimplex.{w} n) := by
  have heq : liftedStdSimplex.{w} n =
      ULift.down ⁻¹' (Set.range
        (fun w : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
          (⇑w.weights : Fin (n + 1) → ℝ))) := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w, rfl⟩
    · intro hx
      obtain ⟨w, hw⟩ := hx
      have hdown : (⇑w.weights : Fin (n + 1) → ℝ) = x.down := hw
      refine ⟨w, ?_⟩
      have hup : ULift.up (⇑w.weights :
          Fin (n + 1) → ℝ) = x := by
        rw [hdown]
      exact hup
  rw [heq]
  exact (convex_range_weights n).linear_preimage ULift.moduleEquiv.toLinearMap

noncomputable def liftedStdAffine (n : ℕ) :
    Fin (n + 1) → ULift.{w} (Fin (n + 1) → ℝ) :=
  fun i => ULift.up (⇑(Convexity.StdSimplex.single i :
    Convexity.StdSimplex ℝ (Fin (n + 1))).weights)

lemma liftedStdAffine_mem_liftedStdSimplex (n : ℕ) :
    ∀ i, liftedStdAffine.{w} n i ∈ liftedStdSimplex.{w} n := by
  intro i
  exact ⟨_, rfl⟩

lemma subdivSimplices_liftedStdAffine_mem {n : ℕ}
    {τ : Fin (n + 1) → ULift.{w} (Fin (n + 1) → ℝ)}
    (hτ : τ ∈ subdivSimplices (liftedStdAffine.{w} n))
    (i : Fin (n + 1)) :
    τ i ∈ liftedStdSimplex.{w} n := by
  have hmem : Set.range τ ⊆ convexHull ℝ (Set.range (liftedStdAffine.{w} n)) := hτ.1
  have hconv := convexHull_min
    (by rw [Set.range_subset_iff]; exact liftedStdAffine_mem_liftedStdSimplex n)
    (convex_liftedStdSimplex n)
  exact hconv (hmem (Set.mem_range_self i))

noncomputable def liftedStdSimplexHomeo (n : ℕ) :
    (liftedStdSimplex.{w} n : Type w) ≃ₜ
      ULift.{w} (Convexity.StdSimplex ℝ (Fin (n + 1))) where
  toFun y :=
    ULift.up
      { weights := Finsupp.equivFunOnFinite.symm (y.val.down)
        nonneg := by
          obtain ⟨w, hw⟩ := y.property
          have hdown : y.val.down = ⇑w.weights := by
            rw [← hw]
          have heq : Finsupp.equivFunOnFinite.symm (y.val.down) = w.weights := by
            rw [hdown, Finsupp.equivFunOnFinite_symm_coe]
          rw [heq]
          exact w.nonneg
        total := by
          obtain ⟨w, hw⟩ := y.property
          have hdown : y.val.down = ⇑w.weights := by
            rw [← hw]
          have heq : Finsupp.equivFunOnFinite.symm (y.val.down) = w.weights := by
            rw [hdown, Finsupp.equivFunOnFinite_symm_coe]
          calc (Finsupp.equivFunOnFinite.symm (y.val.down)).sum (fun _ r => r)
              = w.weights.sum (fun _ r => r) := by rw [heq]
            _ = 1 := w.total }
  invFun z :=
    ⟨ULift.up (⇑(z.down).weights), ⟨z.down, rfl⟩⟩
  left_inv y := by
    obtain ⟨yval, hy⟩ := y
    apply Subtype.ext
    change ULift.up (⇑(Finsupp.equivFunOnFinite.symm (yval.down) :
      Fin (n + 1) →₀ ℝ)) = yval
    rw [Finsupp.coe_equivFunOnFinite_symm, ULift.up_down]
  right_inv z := by
    apply ULift.down_injective
    apply Convexity.StdSimplex.ext
    change Finsupp.equivFunOnFinite.symm
        ((ULift.up (⇑(z.down).weights) :
          ULift.{w} (Fin (n + 1) → ℝ)).down) = (z.down).weights
    have hdown : ((ULift.up (⇑(z.down).weights) :
      ULift.{w} (Fin (n + 1) → ℝ)).down) = ⇑(z.down).weights := rfl
    rw [hdown, Finsupp.equivFunOnFinite_symm_coe]
  continuous_toFun := by
    have h_emb := Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
      (Fin (n + 1))
    have h_down_emb : Topology.IsEmbedding
        (ULift.down : ULift.{w} (Convexity.StdSimplex ℝ (Fin (n + 1))) →
          Convexity.StdSimplex ℝ (Fin (n + 1))) :=
      Homeomorph.ulift.isEmbedding
    rw [h_down_emb.continuous_iff, h_emb.continuous_iff]
    exact Homeomorph.ulift.continuous_toFun.comp continuous_subtype_val
  continuous_invFun := by
    have h_down_emb : Topology.IsEmbedding
        (ULift.down : ULift.{w} (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) :=
      Homeomorph.ulift.isEmbedding
    apply Continuous.subtype_mk
    rw [h_down_emb.continuous_iff, continuous_pi_iff]
    intro i
    exact (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i).comp
      Homeomorph.ulift.continuous_toFun

noncomputable def liftedStdSimplexTopHom (n : ℕ) :
    TopCat.of (liftedStdSimplex.{w} n) ⟶
      SimplexCategory.toTop.{w}.obj ⦋n⦌ :=
  TopCat.ofHom ⟨liftedStdSimplexHomeo.{w} n,
    (liftedStdSimplexHomeo.{w} n).continuous⟩

/-- Compatibility of the lifted `Top` homeomorphism with affine
realization: the lifted homeomorphism sends the affine realization
inside `liftedStdSimplex` to the underlying simplex point. -/
theorem liftedStdSimplexTopHom_affineRealizeIn_liftedStdAffine_apply
    (n : ℕ) (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (ConcreteCategory.hom (liftedStdSimplexTopHom.{w} n))
        (affineRealizeIn (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)
          (liftedStdAffine.{w} n)
          (liftedStdAffine_mem_liftedStdSimplex.{w} n) w) =
      (TopCat.uliftFunctorObjHomeo
        (SimplexCategory.toTop₀.obj (SimplexCategory.mk n))) w := by
  apply ULift.down_injective
  have h_rhs : ((TopCat.uliftFunctorObjHomeo
      (SimplexCategory.toTop₀.obj (SimplexCategory.mk n))) w).down = w := rfl
  have h_lhs : ((ConcreteCategory.hom (liftedStdSimplexTopHom.{w} n))
        (affineRealizeIn (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)
          (liftedStdAffine.{w} n)
          (liftedStdAffine_mem_liftedStdSimplex.{w} n) w)).down = w := by
    have h_down_affine : (affineRealize (liftedStdAffine.{w} n) w).down =
        ⇑w.weights := by
      rw [affineRealize_apply]
      have hdown_eq : ∀ y : ULift.{w} (Fin (n + 1) → ℝ),
          y.down = ⇑(ULift.moduleEquiv : ULift.{w} (Fin (n + 1) → ℝ) ≃ₗ[ℝ]
            (Fin (n + 1) → ℝ)) y := fun y => rfl
      rw [hdown_eq]
      simp only [map_sum, map_smul, liftedStdAffine, ULift.moduleEquiv_apply,
        Convexity.StdSimplex.weights_single, Finsupp.single_eq_pi_single]
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ j]
      simp
    have h_weights : Finsupp.equivFunOnFinite.symm
        ((affineRealize (liftedStdAffine.{w} n) w).down) = w.weights := by
      rw [h_down_affine, Finsupp.equivFunOnFinite_symm_coe]
    have h_homeo_weights : (((liftedStdSimplexHomeo.{w} n)
        (affineRealizeIn (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)
          (liftedStdAffine.{w} n)
          (liftedStdAffine_mem_liftedStdSimplex.{w} n) w)).down).weights =
        Finsupp.equivFunOnFinite.symm
          ((affineRealize (liftedStdAffine.{w} n) w).down) := rfl
    have h_equiv : (liftedStdSimplexHomeo.{w} n
        (affineRealizeIn (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)
          (liftedStdAffine.{w} n)
          (liftedStdAffine_mem_liftedStdSimplex.{w} n) w)).down = w := by
      apply Convexity.StdSimplex.ext
      rw [h_homeo_weights]
      exact h_weights
    have h_app : (ConcreteCategory.hom (liftedStdSimplexTopHom.{w} n))
          (affineRealizeIn (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)
            (liftedStdAffine.{w} n)
            (liftedStdAffine_mem_liftedStdSimplex.{w} n) w) =
        liftedStdSimplexHomeo.{w} n
          (affineRealizeIn (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)
            (liftedStdAffine.{w} n)
            (liftedStdAffine_mem_liftedStdSimplex.{w} n) w) := rfl
    have h_down : ((ConcreteCategory.hom (liftedStdSimplexTopHom.{w} n))
          (affineRealizeIn (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)
            (liftedStdAffine.{w} n)
            (liftedStdAffine_mem_liftedStdSimplex.{w} n) w)).down = w := by
      rw [h_app]
      exact h_equiv
    exact h_down
  rw [h_lhs, h_rhs]

noncomputable def univSubdivULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (n : ℕ) :
    R ⟶ (((SSet.chainComplexFunctor C).obj R).obj
      (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n⦌))).X n :=
  SSet.ιChainComplex
      (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
      (liftedStdAffine.{w} n) ≫
    subdivision R (ULift.{w} (Fin (n + 1) → ℝ)) n ≫
    liftIn R (liftedStdSimplex.{w} n) n ≫
    (realizeInChain R (liftedStdSimplex.{w} n)
      (convex_liftedStdSimplex.{w} n)).f n ≫
    (((SSet.chainComplexFunctor C).obj R).map
      (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f n

noncomputable def univHomotopyULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (n : ℕ) :
    R ⟶ (((SSet.chainComplexFunctor C).obj R).obj
      (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n⦌))).X (n + 1) :=
  SSet.ιChainComplex
      (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
      (liftedStdAffine.{w} n) ≫
    homotopyOp R (ULift.{w} (Fin (n + 1) → ℝ)) n ≫
    liftIn R (liftedStdSimplex.{w} n) (n + 1) ≫
    (realizeInChain R (liftedStdSimplex.{w} n)
      (convex_liftedStdSimplex.{w} n)).f (n + 1) ≫
    (((SSet.chainComplexFunctor C).obj R).map
      (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f (n + 1)

noncomputable def univFundULift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (n : ℕ) :
    R ⟶ (((SSet.chainComplexFunctor C).obj R).obj
      (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n⦌))).X n :=
  SSet.ιChainComplex
      (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
      (liftedStdAffine.{w} n) ≫
    liftIn R (liftedStdSimplex.{w} n) n ≫
    (realizeInChain R (liftedStdSimplex.{w} n)
      (convex_liftedStdSimplex.{w} n)).f n ≫
    (((SSet.chainComplexFunctor C).obj R).map
      (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma univSubdivULift_naturality_coefficient
    {D : Type u} [Category.{v} D] [Preadditive D] [HasCoproducts.{w} D]
    {R S : D} (a : R ⟶ S) (n : ℕ) :
    univSubdivULift (C := D) R n ≫
        (((SSet.chainComplexFunctor D).map a).app
          (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n⦌))).f n =
      a ≫ univSubdivULift (C := D) S n := by
  have hReal :
      (realizeInChain (C := D) R (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f n ≫
        (((SSet.chainComplexFunctor D).map a).app
          (TopCat.toSSet.obj (TopCat.of (liftedStdSimplex.{w} n)))).f n =
      (((SSet.chainComplexFunctor D).map a).app
          (linSSetIn (ULift.{w} (Fin (n + 1) → ℝ))
            (liftedStdSimplex.{w} n))).f n ≫
        (realizeInChain (C := D) S (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f n := by
    have h := realizeInChain_naturality_coefficient (C := D) (a := a)
      (V := ULift.{w} (Fin (n + 1) → ℝ))
      (K := liftedStdSimplex.{w} n)
      (hK := convex_liftedStdSimplex.{w} n)
    have h2 := congrArg (fun φ => φ.f n) h
    simpa using h2
  have hLift := liftIn_naturality_coefficient (C := D) (a := a)
    (V := ULift.{w} (Fin (n + 1) → ℝ))
    (K := liftedStdSimplex.{w} n) (n := n)
  have hSub := subdivision_naturality_coefficient (C := D) (a := a)
    (V := ULift.{w} (Fin (n + 1) → ℝ)) (n := n)
  have hTop := ((SSet.chainComplexFunctor D).map a).naturality
    (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))
  have hTop' := congrArg (fun φ => φ.f n) hTop
  simp only [HomologicalComplex.comp_f] at hTop'
  let tR := subdivision (C := D) R (ULift.{w} (Fin (n + 1) → ℝ)) n ≫
    liftIn (C := D) R (liftedStdSimplex.{w} n) n ≫
    (realizeInChain (C := D) R (liftedStdSimplex.{w} n)
      (convex_liftedStdSimplex.{w} n)).f n ≫
    (((SSet.chainComplexFunctor D).obj R).map
      (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f n
  let tS := subdivision (C := D) S (ULift.{w} (Fin (n + 1) → ℝ)) n ≫
    liftIn (C := D) S (liftedStdSimplex.{w} n) n ≫
    (realizeInChain (C := D) S (liftedStdSimplex.{w} n)
      (convex_liftedStdSimplex.{w} n)).f n ≫
    (((SSet.chainComplexFunctor D).obj S).map
      (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f n
  have hT : tR ≫
      (((SSet.chainComplexFunctor D).map a).app
        (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n⦌))).f n =
    (((SSet.chainComplexFunctor D).map a).app
      (linSSet (ULift.{w} (Fin (n + 1) → ℝ)))).f n ≫ tS := by
    dsimp only [tR, tS]
    slice_lhs 4 5 => rw [hTop']
    slice_lhs 3 4 => rw [hReal]
    slice_lhs 2 3 => rw [hLift]
    slice_lhs 1 2 => rw [hSub]
    simp only [Category.assoc]
  change (SSet.ιChainComplex
      (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
      (liftedStdAffine.{w} n) ≫ tR) ≫ _ =
    a ≫ SSet.ιChainComplex
      (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := S)
      (liftedStdAffine.{w} n) ≫ tS
  rw [Category.assoc, hT, ← Category.assoc,
    SSet.ιChainComplex_coefficientMap_f, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma univHomotopyULift_naturality_coefficient
    {D : Type u} [Category.{v} D] [Preadditive D] [HasCoproducts.{w} D]
    {R S : D} (a : R ⟶ S) (n : ℕ) :
    univHomotopyULift (C := D) R n ≫
        (((SSet.chainComplexFunctor D).map a).app
          (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n⦌))).f (n + 1) =
      a ≫ univHomotopyULift (C := D) S n := by
  have hReal :
      (realizeInChain (C := D) R (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f (n + 1) ≫
        (((SSet.chainComplexFunctor D).map a).app
          (TopCat.toSSet.obj (TopCat.of (liftedStdSimplex.{w} n)))).f (n + 1) =
      (((SSet.chainComplexFunctor D).map a).app
          (linSSetIn (ULift.{w} (Fin (n + 1) → ℝ))
            (liftedStdSimplex.{w} n))).f (n + 1) ≫
        (realizeInChain (C := D) S (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f (n + 1) := by
    have h := realizeInChain_naturality_coefficient (C := D) (a := a)
      (V := ULift.{w} (Fin (n + 1) → ℝ))
      (K := liftedStdSimplex.{w} n)
      (hK := convex_liftedStdSimplex.{w} n)
    have h2 := congrArg (fun φ => φ.f (n + 1)) h
    simpa using h2
  have hLift := liftIn_naturality_coefficient (C := D) (a := a)
    (V := ULift.{w} (Fin (n + 1) → ℝ))
    (K := liftedStdSimplex.{w} n) (n := n + 1)
  have hHom := homotopyOp_naturality_coefficient (C := D) (a := a)
    (V := ULift.{w} (Fin (n + 1) → ℝ)) (n := n)
  have hTop := ((SSet.chainComplexFunctor D).map a).naturality
    (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))
  have hTop' := congrArg (fun φ => φ.f (n + 1)) hTop
  simp only [HomologicalComplex.comp_f] at hTop'
  let tR := homotopyOp (C := D) R (ULift.{w} (Fin (n + 1) → ℝ)) n ≫
    liftIn (C := D) R (liftedStdSimplex.{w} n) (n + 1) ≫
    (realizeInChain (C := D) R (liftedStdSimplex.{w} n)
      (convex_liftedStdSimplex.{w} n)).f (n + 1) ≫
    (((SSet.chainComplexFunctor D).obj R).map
      (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f (n + 1)
  let tS := homotopyOp (C := D) S (ULift.{w} (Fin (n + 1) → ℝ)) n ≫
    liftIn (C := D) S (liftedStdSimplex.{w} n) (n + 1) ≫
    (realizeInChain (C := D) S (liftedStdSimplex.{w} n)
      (convex_liftedStdSimplex.{w} n)).f (n + 1) ≫
    (((SSet.chainComplexFunctor D).obj S).map
      (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f (n + 1)
  have hT : tR ≫
      (((SSet.chainComplexFunctor D).map a).app
        (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n⦌))).f (n + 1) =
    (((SSet.chainComplexFunctor D).map a).app
      (linSSet (ULift.{w} (Fin (n + 1) → ℝ)))).f n ≫ tS := by
    dsimp only [tR, tS]
    slice_lhs 4 5 => rw [hTop']
    slice_lhs 3 4 => rw [hReal]
    slice_lhs 2 3 => rw [hLift]
    slice_lhs 1 2 => rw [hHom]
    simp only [Category.assoc]
  change (SSet.ιChainComplex
      (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
      (liftedStdAffine.{w} n) ≫ tR) ≫ _ =
    a ≫ SSet.ιChainComplex
      (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := S)
      (liftedStdAffine.{w} n) ≫ tS
  rw [Category.assoc, hT, ← Category.assoc,
    SSet.ιChainComplex_coefficientMap_f, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma univFundULift_naturality_coefficient
    {D : Type u} [Category.{v} D] [Preadditive D] [HasCoproducts.{w} D]
    {R S : D} (a : R ⟶ S) (n : ℕ) :
    univFundULift (C := D) R n ≫
        (((SSet.chainComplexFunctor D).map a).app
          (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n⦌))).f n =
      a ≫ univFundULift (C := D) S n := by
  have hReal :
      (realizeInChain (C := D) R (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f n ≫
        (((SSet.chainComplexFunctor D).map a).app
          (TopCat.toSSet.obj (TopCat.of (liftedStdSimplex.{w} n)))).f n =
      (((SSet.chainComplexFunctor D).map a).app
          (linSSetIn (ULift.{w} (Fin (n + 1) → ℝ))
            (liftedStdSimplex.{w} n))).f n ≫
        (realizeInChain (C := D) S (liftedStdSimplex.{w} n)
          (convex_liftedStdSimplex.{w} n)).f n := by
    have h := realizeInChain_naturality_coefficient (C := D) (a := a)
      (V := ULift.{w} (Fin (n + 1) → ℝ))
      (K := liftedStdSimplex.{w} n)
      (hK := convex_liftedStdSimplex.{w} n)
    have h2 := congrArg (fun φ => φ.f n) h
    simpa using h2
  have hLift := liftIn_naturality_coefficient (C := D) (a := a)
    (V := ULift.{w} (Fin (n + 1) → ℝ))
    (K := liftedStdSimplex.{w} n) (n := n)
  have hTop := ((SSet.chainComplexFunctor D).map a).naturality
    (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))
  have hTop' := congrArg (fun φ => φ.f n) hTop
  simp only [HomologicalComplex.comp_f] at hTop'
  let tR := liftIn (C := D) R (liftedStdSimplex.{w} n) n ≫
    (realizeInChain (C := D) R (liftedStdSimplex.{w} n)
      (convex_liftedStdSimplex.{w} n)).f n ≫
    (((SSet.chainComplexFunctor D).obj R).map
      (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f n
  let tS := liftIn (C := D) S (liftedStdSimplex.{w} n) n ≫
    (realizeInChain (C := D) S (liftedStdSimplex.{w} n)
      (convex_liftedStdSimplex.{w} n)).f n ≫
    (((SSet.chainComplexFunctor D).obj S).map
      (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f n
  have hT : tR ≫
      (((SSet.chainComplexFunctor D).map a).app
        (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n⦌))).f n =
    (((SSet.chainComplexFunctor D).map a).app
      (linSSet (ULift.{w} (Fin (n + 1) → ℝ)))).f n ≫ tS := by
    dsimp only [tR, tS]
    slice_lhs 3 4 => rw [hTop']
    slice_lhs 2 3 => rw [hReal]
    slice_lhs 1 2 => rw [hLift]
    simp only [Category.assoc]
  change (SSet.ιChainComplex
      (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
      (liftedStdAffine.{w} n) ≫ tR) ≫ _ =
    a ≫ SSet.ιChainComplex
      (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := S)
      (liftedStdAffine.{w} n) ≫ tS
  rw [Category.assoc, hT, ← Category.assoc,
    SSet.ιChainComplex_coefficientMap_f, Category.assoc]

end LiftedStdSimplex

noncomputable def affineTopIn {V W : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (K : Set V) (L : Set W) (f : V →ₗ[ℝ] W)
    (hf : Set.MapsTo f K L) : TopCat.of (↥K) ⟶ TopCat.of (↥L) :=
  TopCat.ofHom
    ⟨fun x => ⟨f x.1, hf x.2⟩,
      Continuous.subtype_mk
        (f.continuous_of_finiteDimensional.comp continuous_subtype_val) (fun x => hf x.2)⟩

lemma affineRealizeIn_comp_linear_set {V W : Type w} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] {K : Set V} {L : Set W}
    (hK : Convex ℝ K) (hL : Convex ℝ L) {n : ℕ} (f : V →ₗ[ℝ] W)
    (hf : Set.MapsTo f K L) (τ : Fin (n + 1) → V) (hτ : ∀ i, τ i ∈ K) :
    affineRealizeIn L hL (f ∘ τ) (fun i => hf (hτ i)) =
      (affineTopIn K L f hf).hom.comp (affineRealizeIn K hK τ hτ) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change affineRealize (f ∘ τ) x = f (affineRealize τ x)
  exact affineRealize_comp_linear f τ x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma affine_bridge_aux_set {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] {R : C} {V W : Type w} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W] {K : Set V} {L : Set W}
    (hK : Convex ℝ K) (hL : Convex ℝ L) {n : ℕ} {X : Set (Fin (n + 1) → V)}
    (hX : ∀ τ ∈ X, ∀ i, τ i ∈ K) (f : V →ₗ[ℝ] W) (hf : Set.MapsTo f K L)
    (τ : Fin (n + 1) → V) (hτ : τ ∈ X) :
    SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫
        ((linearChainComplexFunctor (C := C) R).map (TypeCat.ofHom f)).f n ≫
          liftIn (C := C) R L n ≫ (realizeInChain (C := C) R L hL).f n =
      SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫
        liftIn (C := C) R K n ≫ (realizeInChain (C := C) R K hK).f n ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (affineTopIn K L f hf))).f n := by
  have hτK : ∀ i, τ i ∈ K := hX τ hτ
  have hτL : ∀ i, (f ∘ τ) i ∈ L := fun i => hf (hτK i)
  let src : (TopCat.toSSet.obj (TopCat.of (↥K))).obj (Opposite.op ⦋n⦌) :=
    ((TopCat.of (↥K)).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm
      (affineRealizeIn K hK τ hτK)
  let mid : (TopCat.toSSet.obj (TopCat.of (↥L))).obj (Opposite.op ⦋n⦌) :=
    ((TopCat.of (↥L)).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm
      (affineRealizeIn L hL (f ∘ τ) hτL)
  have left_eq :
      SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫
          ((linearChainComplexFunctor (C := C) R).map (TypeCat.ofHom f)).f n ≫
            liftIn (C := C) R L n ≫ (realizeInChain (C := C) R L hL).f n =
        SSet.ιChainComplex
          (X := TopCat.toSSet.obj (TopCat.of (↥L))) (R := R) mid := by
    have hmap := linearChainComplexFunctor_map_ι (C := C) R f τ
    dsimp only [SSet.ιChainComplex] at hmap ⊢
    slice_lhs 1 2 => rw [hmap]
    slice_lhs 1 2 =>
      erw [liftIn_ι (C := C) (R := R) (K := L) (n := n) (τ := f ∘ τ), dite_eq_left hτL]
    erw [realizeInChain_ι (C := C) (R := R) (K := L) (hK := hL) (n := n)
      (σ := (⟨f ∘ τ, hτL⟩ : (linSSetIn W L).obj (Opposite.op ⦋n⦌)))]
    rfl
  have right_eq :
      SSet.ιChainComplex (X := linSSet V) (R := R) τ ≫
          liftIn (C := C) R K n ≫ (realizeInChain (C := C) R K hK).f n ≫
            (((SSet.chainComplexFunctor C).obj R).map
              (TopCat.toSSet.map (affineTopIn K L f hf))).f n =
        SSet.ιChainComplex
          (X := TopCat.toSSet.obj (TopCat.of (↥L))) (R := R) mid := by
    slice_lhs 1 2 =>
      erw [liftIn_ι (C := C) (R := R) (K := K) (n := n) (τ := τ), dite_eq_left hτK]
    slice_lhs 1 2 =>
      erw [realizeInChain_ι (C := C) (R := R) (K := K) (hK := hK) (n := n)
        (σ := (⟨τ, hτK⟩ : (linSSetIn V K).obj (Opposite.op ⦋n⦌)))]
    change SSet.ιChainComplex (X := TopCat.toSSet.obj (TopCat.of (↥K))) (R := R) src ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (affineTopIn K L f hf))).f n = _
    erw [SSet.ι_chainComplexMap_f]
    congr 1
    apply (TopCat.toSSetObjEquiv (TopCat.of (↥L)) (Opposite.op ⦋n⦌)).injective
    change (affineTopIn K L f hf).hom.comp (affineRealizeIn K hK τ hτK) =
      affineRealizeIn L hL (f ∘ τ) hτL
    exact (affineRealizeIn_comp_linear_set hK hL f hf τ hτK).symm
  exact left_eq.trans right_eq.symm

lemma affine_bridge_set {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] {R : C} {V W : Type w} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W] {K : Set V} {L : Set W}
    (hK : Convex ℝ K) (hL : Convex ℝ L) {n : ℕ} {X : Set (Fin (n + 1) → V)}
    (hX : ∀ τ ∈ X, ∀ i, τ i ∈ K) (f : V →ₗ[ℝ] W) (hf : Set.MapsTo f K L)
    {c : R ⟶ (freemod (C := C) R V).obj (Opposite.op ⦋n⦌)} (hc : c ∈ chainSpan (C := C) R n X) :
    c ≫ ((linearChainComplexFunctor (C := C) R).map (TypeCat.ofHom f)).f n ≫
        liftIn (C := C) R L n ≫ (realizeInChain (C := C) R L hL).f n =
      c ≫ liftIn (C := C) R K n ≫ (realizeInChain (C := C) R K hK).f n ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (affineTopIn K L f hf))).f n := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨τ, hτ, rfl⟩ := hx
    exact affine_bridge_aux_set hK hL hX f hf τ hτ
  | zero => simp only [zero_comp]
  | add x y _ _ ihx ihy => simp only [Preadditive.add_comp, ihx, ihy]
  | neg x _ ihx => simp only [Preadditive.neg_comp, ihx]

noncomputable def liftedCofaceLinearMap {n : ℕ} (i : Fin (n + 2)) :
    ULift.{w} (Fin (n + 1) → ℝ) →ₗ[ℝ]
      ULift.{w} (Fin (n + 2) → ℝ) :=
  ULift.moduleEquiv.symm.toLinearMap.comp
    ((FunOnFinite.linearMap ℝ ℝ (Fin.succAbove i)).comp
      ULift.moduleEquiv.toLinearMap)

private lemma coface_weights_eq {n : ℕ} (i : Fin (n + 2))
    (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    FunOnFinite.linearMap ℝ ℝ (Fin.succAbove i) ⇑w.weights =
      ⇑(w.map (Fin.succAbove i)).weights := by
  funext j
  rw [FunOnFinite.linearMap_apply_apply]
  have h1 : (w.map (Fin.succAbove i)).weights =
      Finsupp.mapDomain (Fin.succAbove i) w.weights := rfl
  have h2 : ((w.map (Fin.succAbove i)).weights : Fin (n + 2) → ℝ) j =
      ∑ k ∈ Finset.univ.filter (fun k => Fin.succAbove i k = j), w.weights k := by
    rw [h1, Finsupp.mapDomain_fintype]
    rw [Finsupp.finsetSum_apply]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : Fin.succAbove i k = j
    · simp [h]
    · simp [h]
  rw [h2]

lemma liftedCofaceLinearMap_mem {n : ℕ} (i : Fin (n + 2)) :
    Set.MapsTo (liftedCofaceLinearMap.{w} i)
      (liftedStdSimplex.{w} n) (liftedStdSimplex.{w} (n + 1)) := by
  intro x hx
  obtain ⟨w, rfl⟩ := hx
  refine ⟨w.map (Fin.succAbove i), ?_⟩
  apply ULift.down_injective
  change (ULift.up (⇑(w.map (Fin.succAbove i)).weights) :
    ULift.{w} (Fin (n + 2) → ℝ)).down =
    (liftedCofaceLinearMap.{w} i (ULift.up (⇑w.weights))).down
  rw [ULift.down_up]
  have hlin : (liftedCofaceLinearMap.{w} i (ULift.up (⇑w.weights))).down =
      FunOnFinite.linearMap ℝ ℝ (Fin.succAbove i) ⇑w.weights := by
    simp [liftedCofaceLinearMap]
  rw [hlin]
  exact (coface_weights_eq i w).symm

noncomputable def liftedCofaceTop {n : ℕ} (i : Fin (n + 2)) :
    TopCat.of (liftedStdSimplex.{w} n) ⟶
      TopCat.of (liftedStdSimplex.{w} (n + 1)) :=
  affineTopIn (liftedStdSimplex.{w} n) (liftedStdSimplex.{w} (n + 1))
    (liftedCofaceLinearMap.{w} i)
    (liftedCofaceLinearMap_mem.{w} i)

lemma liftedStdSimplexTopHom_naturality_coface {n : ℕ}
    (i : Fin (n + 2)) :
    liftedCofaceTop.{w} i ≫ liftedStdSimplexTopHom.{w} (n + 1) =
      liftedStdSimplexTopHom.{w} n ≫
        SimplexCategory.toTop.{w}.map (SimplexCategory.δ i) := by
  apply TopCat.hom_ext
  ext x
  obtain ⟨xval, hx⟩ := x
  obtain ⟨wx, rfl⟩ := hx
  have h_comp : (liftedCofaceTop.{w} i ≫ liftedStdSimplexTopHom.{w} (n + 1))
      (⟨ULift.up (⇑wx.weights), ⟨wx, rfl⟩⟩ :
        (liftedStdSimplex.{w} n : Type w)) =
      (liftedStdSimplexTopHom.{w} (n + 1))
        ((liftedCofaceTop.{w} i)
          (⟨ULift.up (⇑wx.weights), ⟨wx, rfl⟩⟩ :
            (liftedStdSimplex.{w} n : Type w))) := rfl
  have h_coface_app : (liftedCofaceTop.{w} i)
      (⟨ULift.up (⇑wx.weights), ⟨wx, rfl⟩⟩ :
        (liftedStdSimplex.{w} n : Type w)) =
      (⟨liftedCofaceLinearMap.{w} i (ULift.up (⇑wx.weights)),
        liftedCofaceLinearMap_mem.{w} i ⟨wx, rfl⟩⟩ :
        (liftedStdSimplex.{w} (n + 1) : Type w)) := rfl
  have h_lin : (liftedCofaceLinearMap.{w} i (ULift.up (⇑wx.weights))).down =
      FunOnFinite.linearMap ℝ ℝ (Fin.succAbove i) ⇑wx.weights := by
    simp [liftedCofaceLinearMap]
  have h_weights : Finsupp.equivFunOnFinite.symm
      ((liftedCofaceLinearMap.{w} i (ULift.up (⇑wx.weights))).down) =
      (wx.map (Fin.succAbove i)).weights := by
    rw [h_lin, coface_weights_eq]
    rw [Finsupp.equivFunOnFinite_symm_coe]
  have h_top : (liftedStdSimplexTopHom.{w} n)
      (⟨ULift.up (⇑wx.weights), ⟨wx, rfl⟩⟩ :
        (liftedStdSimplex.{w} n : Type w)) =
      ULift.up wx := by
    apply ULift.down_injective
    apply Convexity.StdSimplex.ext
    change Finsupp.equivFunOnFinite.symm
      ((ULift.up (⇑wx.weights) :
        ULift.{w} (Fin (n + 1) → ℝ)).down) = wx.weights
    have hdown : ((ULift.up (⇑wx.weights) :
      ULift.{w} (Fin (n + 1) → ℝ)).down) = ⇑wx.weights := rfl
    rw [hdown, Finsupp.equivFunOnFinite_symm_coe]
  have h_lhs : (liftedCofaceTop.{w} i ≫ liftedStdSimplexTopHom.{w} (n + 1))
      (⟨ULift.up (⇑wx.weights), ⟨wx, rfl⟩⟩ :
        (liftedStdSimplex.{w} n : Type w)) =
      ULift.up (wx.map (Fin.succAbove i)) := by
    rw [h_comp, h_coface_app]
    apply ULift.down_injective
    apply Convexity.StdSimplex.ext
    change Finsupp.equivFunOnFinite.symm
        ((liftedCofaceLinearMap.{w} i (ULift.up (⇑wx.weights))).down) =
        (wx.map (Fin.succAbove i)).weights
    exact h_weights
  have h_rhs : (liftedStdSimplexTopHom.{w} n ≫
        SimplexCategory.toTop.{w}.map (SimplexCategory.δ i))
      (⟨ULift.up (⇑wx.weights), ⟨wx, rfl⟩⟩ :
        (liftedStdSimplex.{w} n : Type w)) =
      ULift.up (wx.map (Fin.succAbove i)) := by
    have hcomp : (liftedStdSimplexTopHom.{w} n ≫
        SimplexCategory.toTop.{w}.map (SimplexCategory.δ i))
        (⟨ULift.up (⇑wx.weights), ⟨wx, rfl⟩⟩ :
          (liftedStdSimplex.{w} n : Type w)) =
        SimplexCategory.toTop.{w}.map (SimplexCategory.δ i)
          ((liftedStdSimplexTopHom.{w} n)
            (⟨ULift.up (⇑wx.weights), ⟨wx, rfl⟩⟩ :
              (liftedStdSimplex.{w} n : Type w))) := rfl
    rw [hcomp, h_top]
    rfl
  rw [h_lhs, h_rhs]

lemma liftedStdAffine_comp_succAbove {n : ℕ} (i : Fin (n + 2)) :
    liftedStdAffine.{w} (n + 1) ∘ Fin.succAbove i =
      liftedCofaceLinearMap.{w} i ∘ liftedStdAffine.{w} n := by
  funext j
  apply ULift.down_injective
  change ((liftedStdAffine.{w} (n + 1)) (Fin.succAbove i j)).down =
    ((liftedCofaceLinearMap.{w} i) ((liftedStdAffine.{w} n) j)).down
  have h_lhs : (((liftedStdAffine.{w} (n + 1)) (Fin.succAbove i j)).down :
      Fin (n + 2) → ℝ) =
      ⇑(Convexity.StdSimplex.single (Fin.succAbove i j) :
        Convexity.StdSimplex ℝ (Fin (n + 2))).weights := rfl
  have h_rhs : (((liftedCofaceLinearMap.{w} i)
      ((liftedStdAffine.{w} n) j)).down : Fin (n + 2) → ℝ) =
      FunOnFinite.linearMap ℝ ℝ (Fin.succAbove i)
        ⇑(Convexity.StdSimplex.single j :
          Convexity.StdSimplex ℝ (Fin (n + 1))).weights := by
    simp [liftedCofaceLinearMap, liftedStdAffine]
  have h_map : (Convexity.StdSimplex.single (Fin.succAbove i j) :
      Convexity.StdSimplex ℝ (Fin (n + 2))) =
      (Convexity.StdSimplex.single j :
        Convexity.StdSimplex ℝ (Fin (n + 1))).map (Fin.succAbove i) := by
    rw [Convexity.StdSimplex.map_single]
  rw [h_lhs, h_rhs, h_map, coface_weights_eq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
lemma liftedCoface_bridge
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R : C} {n k : ℕ} (i : Fin (n + 2))
    {X : Set (Fin (k + 1) → ULift.{w} (Fin (n + 1) → ℝ))}
    (hX : ∀ τ ∈ X, ∀ j, τ j ∈ liftedStdSimplex.{w} n)
    {c : R ⟶ (freemod (C := C) R
      (ULift.{w} (Fin (n + 1) → ℝ))).obj (Opposite.op ⦋k⦌)}
    (hc : c ∈ chainSpan (C := C) R k X) :
    c ≫ ((linearChainComplexFunctor R).map
        (TypeCat.ofHom (liftedCofaceLinearMap.{w} i))).f k ≫
      liftIn R (liftedStdSimplex.{w} (n + 1)) k ≫
      (realizeInChain R (liftedStdSimplex.{w} (n + 1))
        (convex_liftedStdSimplex.{w} (n + 1))).f k ≫
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f k =
    c ≫ liftIn R (liftedStdSimplex.{w} n) k ≫
      (realizeInChain R (liftedStdSimplex.{w} n)
        (convex_liftedStdSimplex.{w} n)).f k ≫
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f k ≫
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map
          (SimplexCategory.toTop.{w}.map (SimplexCategory.δ i)))).f k := by
  have hBridge := affine_bridge_set (C := C) (R := R)
    (K := liftedStdSimplex.{w} n) (L := liftedStdSimplex.{w} (n + 1))
    (convex_liftedStdSimplex.{w} n)
    (convex_liftedStdSimplex.{w} (n + 1)) hX
    (liftedCofaceLinearMap.{w} i)
    (liftedCofaceLinearMap_mem.{w} i) hc
  have h := congrArg (fun q => q ≫
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f k) hBridge
  simp only [Category.assoc] at h ⊢
  have hMap :
      (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedCofaceTop.{w} i))).f k ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f k =
      (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} n))).f k ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map
            (SimplexCategory.toTop.{w}.map (SimplexCategory.δ i)))).f k := by
    rw [← HomologicalComplex.comp_f, ← Functor.map_comp, ← Functor.map_comp,
      liftedStdSimplexTopHom_naturality_coface,
      Functor.map_comp, Functor.map_comp, HomologicalComplex.comp_f]
  unfold liftedCofaceTop at hMap
  rw [← hMap]
  simpa only [Category.assoc] using h
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma univSubdivULift_face_term
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R : C} (n : ℕ) (i : Fin (n + 2)) :
    SSet.ιChainComplex (X := linSSet (ULift.{w} (Fin (n + 2) → ℝ))) (R := R)
        (liftedStdAffine.{w} (n + 1) ∘ Fin.succAbove i) ≫
      subdivision R (ULift.{w} (Fin (n + 2) → ℝ)) n ≫
      liftIn R (liftedStdSimplex.{w} (n + 1)) n ≫
      (realizeInChain R (liftedStdSimplex.{w} (n + 1))
        (convex_liftedStdSimplex.{w} (n + 1))).f n ≫
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f n =
    univSubdivULift (C := C) R n ≫
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (SimplexCategory.toTop.{w}.map (SimplexCategory.δ i)))).f n := by
  have hc :
      SSet.ιChainComplex (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
          (liftedStdAffine.{w} n) ≫ subdivision R (ULift.{w} (Fin (n + 1) → ℝ)) n ∈
        chainSpan (C := C) R n (subdivSimplices (liftedStdAffine.{w} n)) := by
    change Sigma.ι (fun _ : Fin (n + 1) → ULift.{w} (Fin (n + 1) → ℝ) => (R : C))
        (liftedStdAffine.{w} n) ≫ subdivision R (ULift.{w} (Fin (n + 1) → ℝ)) n ∈ _
    exact subdivision_mem_chainSpan (C := C) R n (liftedStdAffine.{w} n)
  have hbridge := liftedCoface_bridge (C := C) (R := R) i
    (X := subdivSimplices (liftedStdAffine.{w} n))
    (fun τ hτ j => convexHull_min
      (Set.range_subset_iff.mpr (liftedStdAffine_mem_liftedStdSimplex.{w} n))
      (convex_liftedStdSimplex.{w} n) (hτ.1 (Set.mem_range_self j))) hc
  simp only [univSubdivULift]
  rw [liftedStdAffine_comp_succAbove]
  erw [← linearChainComplexFunctor_map_ι]
  have hnat := subdivision_naturality (C := C)
    (V := ULift.{w} (Fin (n + 1) → ℝ)) (W := ULift.{w} (Fin (n + 2) → ℝ)) R
    (liftedCofaceLinearMap.{w} i) n
  simp only [Category.assoc]
  rw [← reassoc_of% hnat]
  simpa only [Category.assoc] using hbridge

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma univHomotopyULift_face_term
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R : C} (n : ℕ) (i : Fin (n + 2)) :
    SSet.ιChainComplex (X := linSSet (ULift.{w} (Fin (n + 2) → ℝ))) (R := R)
        (liftedStdAffine.{w} (n + 1) ∘ Fin.succAbove i) ≫
      homotopyOp R (ULift.{w} (Fin (n + 2) → ℝ)) n ≫
      liftIn R (liftedStdSimplex.{w} (n + 1)) (n + 1) ≫
      (realizeInChain R (liftedStdSimplex.{w} (n + 1))
        (convex_liftedStdSimplex.{w} (n + 1))).f (n + 1) ≫
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f (n + 1) =
    univHomotopyULift (C := C) R n ≫
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (SimplexCategory.toTop.{w}.map (SimplexCategory.δ i)))).f (n + 1) := by
  have hc :
      SSet.ιChainComplex (X := linSSet (ULift.{w} (Fin (n + 1) → ℝ))) (R := R)
          (liftedStdAffine.{w} n) ≫ homotopyOp R (ULift.{w} (Fin (n + 1) → ℝ)) n ∈
        chainSpan (C := C) R (n + 1)
          (hullSimplices (m := n + 1) (liftedStdAffine.{w} n)) := by
    change Sigma.ι (fun _ : Fin (n + 1) → ULift.{w} (Fin (n + 1) → ℝ) => (R : C))
        (liftedStdAffine.{w} n) ≫ homotopyOp R (ULift.{w} (Fin (n + 1) → ℝ)) n ∈ _
    exact homotopyOp_mem_chainSpan (C := C) R n (liftedStdAffine.{w} n)
  have hbridge := liftedCoface_bridge (C := C) (R := R) i
    (X := hullSimplices (m := n + 1) (liftedStdAffine.{w} n))
    (fun τ hτ j => convexHull_min
      (Set.range_subset_iff.mpr (liftedStdAffine_mem_liftedStdSimplex.{w} n))
      (convex_liftedStdSimplex.{w} n) (hτ (Set.mem_range_self j))) hc
  simp only [univHomotopyULift]
  rw [liftedStdAffine_comp_succAbove]
  erw [← linearChainComplexFunctor_map_ι]
  have hnat := homotopyOp_naturality (C := C)
    (V := ULift.{w} (Fin (n + 1) → ℝ)) (W := ULift.{w} (Fin (n + 2) → ℝ)) R
    (liftedCofaceLinearMap.{w} i) n
  simp only [Category.assoc]
  rw [← reassoc_of% hnat]
  simpa only [Category.assoc] using hbridge

private lemma liftedRealizeMap_comp_d
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (n : ℕ) :
    (realizeInChain R (liftedStdSimplex.{w} (n + 1))
        (convex_liftedStdSimplex.{w} (n + 1))).f (n + 1) ≫
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f (n + 1) ≫
      (((SSet.chainComplexFunctor C).obj R).obj
        (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n + 1⦌))).d (n + 1) n =
    ((linSSetIn (ULift.{w} (Fin (n + 2) → ℝ))
        (liftedStdSimplex.{w} (n + 1))).chainComplex R).d (n + 1) n ≫
      (realizeInChain R (liftedStdSimplex.{w} (n + 1))
        (convex_liftedStdSimplex.{w} (n + 1))).f n ≫
      (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f n := by
  have hReal := (realizeInChain R (liftedStdSimplex.{w} (n + 1))
      (convex_liftedStdSimplex.{w} (n + 1))).comm (n + 1) n
  have hMap := (((SSet.chainComplexFunctor C).obj R).map
      (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).comm (n + 1) n
  calc (realizeInChain R (liftedStdSimplex.{w} (n + 1))
          (convex_liftedStdSimplex.{w} (n + 1))).f (n + 1) ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f (n + 1) ≫
        (((SSet.chainComplexFunctor C).obj R).obj
          (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n + 1⦌))).d (n + 1) n
      = (realizeInChain R (liftedStdSimplex.{w} (n + 1))
          (convex_liftedStdSimplex.{w} (n + 1))).f (n + 1) ≫
        ((((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f (n + 1) ≫
          (((SSet.chainComplexFunctor C).obj R).obj
            (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n + 1⦌))).d (n + 1) n) := by
        rfl
    _ = (realizeInChain R (liftedStdSimplex.{w} (n + 1))
          (convex_liftedStdSimplex.{w} (n + 1))).f (n + 1) ≫
        ((((SSet.chainComplexFunctor C).obj R).obj
            (TopCat.toSSet.obj (TopCat.of (liftedStdSimplex.{w} (n + 1))))).d (n + 1) n ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f n) := by
        rw [hMap]
    _ = ((realizeInChain R (liftedStdSimplex.{w} (n + 1))
          (convex_liftedStdSimplex.{w} (n + 1))).f (n + 1) ≫
          (((SSet.chainComplexFunctor C).obj R).obj
            (TopCat.toSSet.obj (TopCat.of (liftedStdSimplex.{w} (n + 1))))).d (n + 1) n) ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f n := by
        simp only [Category.assoc]
    _ = ((((linSSetIn (ULift.{w} (Fin (n + 2) → ℝ))
          (liftedStdSimplex.{w} (n + 1))).chainComplex R).d (n + 1) n ≫
        (realizeInChain R (liftedStdSimplex.{w} (n + 1))
          (convex_liftedStdSimplex.{w} (n + 1))).f n) ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f n) := by
        rw [hReal]
    _ = ((linSSetIn (ULift.{w} (Fin (n + 2) → ℝ))
          (liftedStdSimplex.{w} (n + 1))).chainComplex R).d (n + 1) n ≫
        (realizeInChain R (liftedStdSimplex.{w} (n + 1))
          (convex_liftedStdSimplex.{w} (n + 1))).f n ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f n := by
        simp only [Category.assoc]

private lemma linSSet_delta_liftedStdAffine {n : ℕ} (i : Fin (n + 2)) :
    (linSSet (ULift.{w} (Fin (n + 2) → ℝ))).δ i
        (liftedStdAffine.{w} (n + 1)) =
      liftedStdAffine.{w} (n + 1) ∘ Fin.succAbove i := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
theorem univSubdivULift_boundary
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (n : ℕ) :
    univSubdivULift (C := C) R (n + 1) ≫
        (((SSet.chainComplexFunctor C).obj R).obj
          (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n + 1⦌))).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (univSubdivULift (C := C) R n ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (SimplexCategory.toTop.{w}.map
              (SimplexCategory.δ i)))).f n) := by
  have hX : ∀ τ ∈ subdivSimplices (liftedStdAffine.{w} (n + 1)),
      ∀ j, τ j ∈ liftedStdSimplex.{w} (n + 1) := by
    intro τ hτ j
    have hmem : Set.range τ ⊆ convexHull ℝ (Set.range (liftedStdAffine.{w} (n + 1))) := hτ.1
    have hHull : convexHull ℝ (Set.range (liftedStdAffine.{w} (n + 1))) ⊆
        liftedStdSimplex.{w} (n + 1) := by
      apply convexHull_min
      · intro y hy
        obtain ⟨k, rfl⟩ := hy
        exact liftedStdAffine_mem_liftedStdSimplex.{w} (n + 1) k
      · exact convex_liftedStdSimplex.{w} (n + 1)
    exact hHull (hmem (Set.mem_range_self j))
  have hc : SSet.ιChainComplex (X := linSSet (ULift.{w} (Fin (n + 2) → ℝ))) (R := R)
        (liftedStdAffine.{w} (n + 1)) ≫ subdivision R (ULift.{w} (Fin (n + 2) → ℝ)) (n + 1) ∈
      chainSpan (C := C) R (n + 1) (subdivSimplices (liftedStdAffine.{w} (n + 1))) := by
    change Sigma.ι (fun _ : Fin (n + 2) → ULift.{w} (Fin (n + 2) → ℝ) => (R : C))
        (liftedStdAffine.{w} (n + 1)) ≫ subdivision R (ULift.{w} (Fin (n + 2) → ℝ)) (n + 1) ∈ _
    exact subdivision_mem_chainSpan (C := C) R (n + 1) (liftedStdAffine.{w} (n + 1))
  have hlift := liftIn_comm_d (C := C) (R := R) (liftedStdSimplex.{w} (n + 1)) hX hc
  have hReal := liftedRealizeMap_comp_d (C := C) R n
  simp only [univSubdivULift, Category.assoc]
  rw [hReal]
  rw [reassoc_of% hlift]
  erw [reassoc_of% (subdivision_comp_d (C := C) R (ULift.{w} (Fin (n + 2) → ℝ)) n)]
  rw [reassoc_of% (SSet.ιChainComplex_d
    (linSSet (ULift.{w} (Fin (n + 2) → ℝ))) R
    (liftedStdAffine.{w} (n + 1)))]
  erw [Preadditive.sum_comp]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  erw [Preadditive.zsmul_comp]
  apply congrArg (fun t => (-1 : ℤ) ^ (i : ℕ) • t)
  rw [linSSet_delta_liftedStdAffine (n := n) i]
  simpa only [univSubdivULift, Category.assoc] using
    (univSubdivULift_face_term (C := C) (R := R) n i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem univHomotopyULift_boundary
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (n : ℕ) :
    univHomotopyULift (C := C) R (n + 1) ≫
        (((SSet.chainComplexFunctor C).obj R).obj
          (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n + 1⦌))).d
            (n + 2) (n + 1) =
      univFundULift (C := C) R (n + 1) -
        univSubdivULift (C := C) R (n + 1) -
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (univHomotopyULift (C := C) R n ≫
            (((SSet.chainComplexFunctor C).obj R).map
              (TopCat.toSSet.map
                (SimplexCategory.toTop.{w}.map
                  (SimplexCategory.δ i)))).f (n + 1)) := by
  have hHull : ∀ τ ∈ hullSimplices (m := n + 2) (liftedStdAffine.{w} (n + 1)),
      ∀ j, τ j ∈ liftedStdSimplex.{w} (n + 1) := by
    intro τ hτ j
    exact convexHull_min
      (Set.range_subset_iff.mpr (liftedStdAffine_mem_liftedStdSimplex.{w} (n + 1)))
      (convex_liftedStdSimplex.{w} (n + 1)) (hτ (Set.mem_range_self j))
  have hc :
      SSet.ιChainComplex (X := linSSet (ULift.{w} (Fin (n + 2) → ℝ))) (R := R)
          (liftedStdAffine.{w} (n + 1)) ≫ homotopyOp R (ULift.{w} (Fin (n + 2) → ℝ)) (n + 1) ∈
        chainSpan (C := C) R (n + 2)
          (hullSimplices (m := n + 2) (liftedStdAffine.{w} (n + 1))) := by
    change Sigma.ι (fun _ : Fin (n + 2) → ULift.{w} (Fin (n + 2) → ℝ) => (R : C))
        (liftedStdAffine.{w} (n + 1)) ≫ homotopyOp R (ULift.{w} (Fin (n + 2) → ℝ)) (n + 1) ∈ _
    exact homotopyOp_mem_chainSpan (C := C) R (n + 1) (liftedStdAffine.{w} (n + 1))
  have hlift := liftIn_comm_d (C := C) (R := R)
    (liftedStdSimplex.{w} (n + 1)) hHull hc
  have hHT :
      homotopyOp R (ULift.{w} (Fin (n + 2) → ℝ)) (n + 1) ≫
          freeBoundary R (ULift.{w} (Fin (n + 2) → ℝ)) (n + 1) =
        𝟙 _ - subdivision R (ULift.{w} (Fin (n + 2) → ℝ)) (n + 1) -
          freeBoundary R (ULift.{w} (Fin (n + 2) → ℝ)) n ≫
            homotopyOp R (ULift.{w} (Fin (n + 2) → ℝ)) n :=
    eq_sub_of_add_eq
      (homotopyOp_homotopy_local (C := C) R (ULift.{w} (Fin (n + 2) → ℝ)) n)
  have hterm3 :
      SSet.ιChainComplex (X := linSSet (ULift.{w} (Fin (n + 2) → ℝ))) (R := R)
          (liftedStdAffine.{w} (n + 1)) ≫
        (freeBoundary R (ULift.{w} (Fin (n + 2) → ℝ)) n ≫
          homotopyOp R (ULift.{w} (Fin (n + 2) → ℝ)) n) ≫
        liftIn R (liftedStdSimplex.{w} (n + 1)) (n + 1) ≫
        (realizeInChain R (liftedStdSimplex.{w} (n + 1))
          (convex_liftedStdSimplex.{w} (n + 1))).f (n + 1) ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (univHomotopyULift (C := C) R n ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map
              (SimplexCategory.toTop.{w}.map
                (SimplexCategory.δ i)))).f (n + 1)) := by
    simp only [Category.assoc]
    rw [freeBoundary_eq_d (C := C)]
    rw [reassoc_of% (SSet.ιChainComplex_d
      (linSSet (ULift.{w} (Fin (n + 2) → ℝ))) R (liftedStdAffine.{w} (n + 1)))]
    erw [Preadditive.sum_comp]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    erw [Preadditive.zsmul_comp]
    apply congrArg (fun f => (-1 : ℤ) ^ (i : ℕ) • f)
    rw [linSSet_delta_liftedStdAffine (n := n) i]
    simpa only [univHomotopyULift, Category.assoc] using
      (univHomotopyULift_face_term (C := C) (R := R) n i)
  have hRealMap :
      (realizeInChain R (liftedStdSimplex.{w} (n + 1))
          (convex_liftedStdSimplex.{w} (n + 1))).f (n + 2) ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f (n + 2) ≫
        (((SSet.chainComplexFunctor C).obj R).obj
          (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n + 1⦌))).d (n + 2) (n + 1) =
      ((linSSetIn (ULift.{w} (Fin (n + 2) → ℝ))
          (liftedStdSimplex.{w} (n + 1))).chainComplex R).d (n + 2) (n + 1) ≫
        (realizeInChain R (liftedStdSimplex.{w} (n + 1))
          (convex_liftedStdSimplex.{w} (n + 1))).f (n + 1) ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f (n + 1) := by
    have hReal := (realizeInChain R (liftedStdSimplex.{w} (n + 1))
        (convex_liftedStdSimplex.{w} (n + 1))).comm (n + 2) (n + 1)
    have hMap := (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).comm (n + 2) (n + 1)
    calc (realizeInChain R (liftedStdSimplex.{w} (n + 1))
            (convex_liftedStdSimplex.{w} (n + 1))).f (n + 2) ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f (n + 2) ≫
          (((SSet.chainComplexFunctor C).obj R).obj
            (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n + 1⦌))).d (n + 2) (n + 1)
        = (realizeInChain R (liftedStdSimplex.{w} (n + 1))
            (convex_liftedStdSimplex.{w} (n + 1))).f (n + 2) ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f (n + 2) ≫
            (((SSet.chainComplexFunctor C).obj R).obj
              (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋n + 1⦌))).d (n + 2) (n + 1) := by
          rfl
      _ = (realizeInChain R (liftedStdSimplex.{w} (n + 1))
            (convex_liftedStdSimplex.{w} (n + 1))).f (n + 2) ≫
          ((((SSet.chainComplexFunctor C).obj R).obj
              (TopCat.toSSet.obj (TopCat.of (liftedStdSimplex.{w} (n + 1))))).d (n + 2) (n + 1) ≫
            (((SSet.chainComplexFunctor C).obj R).map
              (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f (n + 1)) := by
          rw [hMap]
      _ = ((realizeInChain R (liftedStdSimplex.{w} (n + 1))
            (convex_liftedStdSimplex.{w} (n + 1))).f (n + 2) ≫
            (((SSet.chainComplexFunctor C).obj R).obj
              (TopCat.toSSet.obj (TopCat.of (liftedStdSimplex.{w} (n + 1))))).d (n + 2) (n + 1)) ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f (n + 1) := by
          simp only [Category.assoc]
      _ = ((((linSSetIn (ULift.{w} (Fin (n + 2) → ℝ))
            (liftedStdSimplex.{w} (n + 1))).chainComplex R).d (n + 2) (n + 1) ≫
          (realizeInChain R (liftedStdSimplex.{w} (n + 1))
            (convex_liftedStdSimplex.{w} (n + 1))).f (n + 1)) ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f (n + 1)) := by
          rw [hReal]
      _ = ((linSSetIn (ULift.{w} (Fin (n + 2) → ℝ))
            (liftedStdSimplex.{w} (n + 1))).chainComplex R).d (n + 2) (n + 1) ≫
          (realizeInChain R (liftedStdSimplex.{w} (n + 1))
            (convex_liftedStdSimplex.{w} (n + 1))).f (n + 1) ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} (n + 1)))).f (n + 1) := by
          simp only [Category.assoc]
  conv_lhs => rw [univHomotopyULift]
  simp only [Category.assoc]
  rw [hRealMap]
  rw [reassoc_of% hlift]
  erw [← freeBoundary_eq_d (C := C) R (ULift.{w} (Fin (n + 2) → ℝ)) (n + 1)]
  rw [reassoc_of% hHT]
  erw [Preadditive.sub_comp, Preadditive.sub_comp,
    Preadditive.comp_sub, Preadditive.comp_sub, Category.id_comp, hterm3]
  change univFundULift (C := C) R (n + 1) - univSubdivULift (C := C) R (n + 1) - _ = _
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem univHomotopyULift_boundary_zero
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R : C} :
    univHomotopyULift (C := C) R 0 ≫
        (((SSet.chainComplexFunctor C).obj R).obj
          (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋0⦌))).d 1 0 =
      univFundULift (C := C) R 0 - univSubdivULift (C := C) R 0 := by
  have hHull : ∀ τ ∈ hullSimplices (m := 1) (liftedStdAffine.{w} 0),
      ∀ j, τ j ∈ liftedStdSimplex.{w} 0 := by
    intro τ hτ j
    exact convexHull_min
      (Set.range_subset_iff.mpr (liftedStdAffine_mem_liftedStdSimplex.{w} 0))
      (convex_liftedStdSimplex.{w} 0) (hτ (Set.mem_range_self j))
  have hc :
      SSet.ιChainComplex (X := linSSet (ULift.{w} (Fin 1 → ℝ))) (R := R)
          (liftedStdAffine.{w} 0) ≫ homotopyOp R (ULift.{w} (Fin 1 → ℝ)) 0 ∈
        chainSpan (C := C) R 1 (hullSimplices (m := 1) (liftedStdAffine.{w} 0)) := by
    change Sigma.ι (fun _ : Fin 1 → ULift.{w} (Fin 1 → ℝ) => (R : C))
        (liftedStdAffine.{w} 0) ≫ homotopyOp R (ULift.{w} (Fin 1 → ℝ)) 0 ∈ _
    exact homotopyOp_mem_chainSpan (C := C) R 0 (liftedStdAffine.{w} 0)
  have hlift := liftIn_comm_d (C := C) (R := R) (liftedStdSimplex.{w} 0) hHull hc
  have hHT0 :
      homotopyOp R (ULift.{w} (Fin 1 → ℝ)) 0 ≫ freeBoundary R (ULift.{w} (Fin 1 → ℝ)) 0 =
        𝟙 _ - subdivision R (ULift.{w} (Fin 1 → ℝ)) 0 := by
    rw [freeBoundary_eq_d (C := C)]
    exact homotopyOp_zero_comp_d_local (C := C) R (ULift.{w} (Fin 1 → ℝ))
  have hRealMap :
      (realizeInChain R (liftedStdSimplex.{w} 0)
          (convex_liftedStdSimplex.{w} 0)).f 1 ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} 0))).f 1 ≫
        (((SSet.chainComplexFunctor C).obj R).obj
          (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋0⦌))).d 1 0 =
      ((linSSetIn (ULift.{w} (Fin 1 → ℝ))
          (liftedStdSimplex.{w} 0)).chainComplex R).d 1 0 ≫
        (realizeInChain R (liftedStdSimplex.{w} 0)
          (convex_liftedStdSimplex.{w} 0)).f 0 ≫
        (((SSet.chainComplexFunctor C).obj R).map
          (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} 0))).f 0 := by
    have hReal := (realizeInChain R (liftedStdSimplex.{w} 0)
        (convex_liftedStdSimplex.{w} 0)).comm 1 0
    have hMap := (((SSet.chainComplexFunctor C).obj R).map
        (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} 0))).comm 1 0
    calc (realizeInChain R (liftedStdSimplex.{w} 0)
            (convex_liftedStdSimplex.{w} 0)).f 1 ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} 0))).f 1 ≫
          (((SSet.chainComplexFunctor C).obj R).obj
            (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋0⦌))).d 1 0
        = (realizeInChain R (liftedStdSimplex.{w} 0)
            (convex_liftedStdSimplex.{w} 0)).f 1 ≫
          ((((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} 0))).f 1 ≫
          (((SSet.chainComplexFunctor C).obj R).obj
            (TopCat.toSSet.obj (SimplexCategory.toTop.{w}.obj ⦋0⦌))).d 1 0) := by
          rfl
      _ = (realizeInChain R (liftedStdSimplex.{w} 0)
            (convex_liftedStdSimplex.{w} 0)).f 1 ≫
          ((((SSet.chainComplexFunctor C).obj R).obj
              (TopCat.toSSet.obj (TopCat.of (liftedStdSimplex.{w} 0)))).d 1 0 ≫
            (((SSet.chainComplexFunctor C).obj R).map
              (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} 0))).f 0) := by
          rw [hMap]
      _ = ((realizeInChain R (liftedStdSimplex.{w} 0)
            (convex_liftedStdSimplex.{w} 0)).f 1 ≫
            (((SSet.chainComplexFunctor C).obj R).obj
              (TopCat.toSSet.obj (TopCat.of (liftedStdSimplex.{w} 0)))).d 1 0) ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} 0))).f 0 := by
          simp only [Category.assoc]
      _ = ((((linSSetIn (ULift.{w} (Fin 1 → ℝ))
            (liftedStdSimplex.{w} 0)).chainComplex R).d 1 0 ≫
          (realizeInChain R (liftedStdSimplex.{w} 0)
            (convex_liftedStdSimplex.{w} 0)).f 0) ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} 0))).f 0) := by
          rw [hReal]
      _ = ((linSSetIn (ULift.{w} (Fin 1 → ℝ))
            (liftedStdSimplex.{w} 0)).chainComplex R).d 1 0 ≫
          (realizeInChain R (liftedStdSimplex.{w} 0)
            (convex_liftedStdSimplex.{w} 0)).f 0 ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} 0))).f 0 := by
          simp only [Category.assoc]
  conv_lhs => rw [univHomotopyULift]
  simp only [Category.assoc]
  rw [hRealMap]
  rw [reassoc_of% hlift]
  erw [← freeBoundary_eq_d (C := C) R (ULift.{w} (Fin 1 → ℝ)) 0]
  rw [reassoc_of% hHT0]
  erw [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp]
  have hfund :
      univFundULift (C := C) R 0 =
        SSet.ιChainComplex (X := linSSet (ULift.{w} (Fin 1 → ℝ))) (R := R)
            (liftedStdAffine.{w} 0) ≫
          liftIn R (liftedStdSimplex.{w} 0) 0 ≫
          (realizeInChain R (liftedStdSimplex.{w} 0)
            (convex_liftedStdSimplex.{w} 0)).f 0 ≫
          (((SSet.chainComplexFunctor C).obj R).map
            (TopCat.toSSet.map (liftedStdSimplexTopHom.{w} 0))).f 0 := by
    rfl
  have hsub : univSubdivULift (C := C) R 0 = univFundULift (C := C) R 0 := by
    rw [univSubdivULift, univFundULift, subdivision_zero (C := C)]
    unfold SSet.ιChainComplex
    erw [Category.id_comp]
  rw [hfund, hsub, hfund]

/-- The `ULift` of the barycentric linear map determined by a tuple of vertices. -/
noncomputable def liftedSimplexLinMap {n k : ℕ}
    (τ : Fin (k + 1) → ULift.{w} (Fin (n + 1) → ℝ)) :
    ULift.{w} (Fin (k + 1) → ℝ) →ₗ[ℝ]
      ULift.{w} (Fin (n + 1) → ℝ) :=
  ULift.moduleEquiv.symm.toLinearMap.comp
    ((simplexLinMap (ULift.down ∘ τ)).comp
      ULift.moduleEquiv.toLinearMap)

@[simp]
lemma liftedSimplexLinMap_down {n k : ℕ}
    (τ : Fin (k + 1) → ULift.{w} (Fin (n + 1) → ℝ))
    (x : ULift.{w} (Fin (k + 1) → ℝ)) :
    (liftedSimplexLinMap τ x).down =
      simplexLinMap (ULift.down ∘ τ) x.down :=
  rfl

lemma liftedSimplexLinMap_liftedStdAffine {n k : ℕ}
    (τ : Fin (k + 1) → ULift.{w} (Fin (n + 1) → ℝ)) :
    liftedSimplexLinMap τ ∘ liftedStdAffine.{w} k = τ := by
  funext j
  apply ULift.down_injective
  change (liftedSimplexLinMap τ ((liftedStdAffine.{w} k) j)).down = (τ j).down
  rw [liftedSimplexLinMap_down, simplexLinMap_apply]
  have hdown : (((liftedStdAffine.{w} k) j).down : Fin (k + 1) → ℝ) =
      Pi.single j 1 := by
    change (⇑(Convexity.StdSimplex.single j :
      Convexity.StdSimplex ℝ (Fin (k + 1))).weights : Fin (k + 1) → ℝ) =
      Pi.single j 1
    rw [Convexity.StdSimplex.weights_single, Finsupp.single_eq_pi_single]
  rw [hdown]
  simp [Pi.single_apply]

lemma liftedSimplexLinMap_mem {n k : ℕ}
    {τ : Fin (k + 1) → ULift.{w} (Fin (n + 1) → ℝ)}
    (hτ : ∀ i, τ i ∈ liftedStdSimplex.{w} n) :
    Set.MapsTo (liftedSimplexLinMap τ)
      (liftedStdSimplex.{w} k) (liftedStdSimplex.{w} n) := by
  intro x hx
  obtain ⟨w0, rfl⟩ := hx
  have hW : ∀ i, ∃ w : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ULift.up (⇑w.weights) = τ i := fun i => hτ i
  choose W hW using hW
  have hdown_tau : ∀ i, (τ i).down = ⇑(W i).weights := by
    intro i
    rw [← hW i]
  have hdown_x : (ULift.up (⇑w0.weights) :
      ULift.{w} (Fin (k + 1) → ℝ)).down = ⇑w0.weights := rfl
  have hmap_down : (liftedSimplexLinMap τ (ULift.up (⇑w0.weights))).down =
      simplexLinMap (ULift.down ∘ τ) ⇑w0.weights := rfl
  have hs_eq : simplexLinMap (ULift.down ∘ τ) ⇑w0.weights =
      ∑ i, w0.weights i • ⇑(W i).weights := by
    rw [simplexLinMap_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hi : ((ULift.down ∘ τ) i : Fin (n + 1) → ℝ) = ⇑(W i).weights := by
      change (τ i).down = _
      rw [hdown_tau i]
    have hxw : (⇑w0.weights i : ℝ) • ((ULift.down ∘ τ) i : Fin (n + 1) → ℝ) =
        w0.weights i • ⇑(W i).weights := by
      rw [hi]
    exact hxw
  have h_nonneg : ∀ j, 0 ≤
      (simplexLinMap (ULift.down ∘ τ) ⇑w0.weights) j := by
    intro j
    rw [hs_eq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_nonneg (fun i _ => mul_nonneg (w0.weights_nonneg i)
      ((W i).weights_nonneg j))
  have h_sum : ∑ j, (simplexLinMap (ULift.down ∘ τ) ⇑w0.weights) j = 1 := by
    rw [hs_eq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc ∑ j : Fin (n + 1), ∑ i : Fin (k + 1), w0.weights i * (W i).weights j
        = ∑ i : Fin (k + 1), ∑ j : Fin (n + 1), w0.weights i * (W i).weights j := by
          rw [Finset.sum_comm]
      _ = ∑ i : Fin (k + 1), w0.weights i * ∑ j : Fin (n + 1), (W i).weights j := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ i : Fin (k + 1), w0.weights i * 1 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [(W i).total_of_fintype]
      _ = 1 := by
          simp [w0.total_of_fintype]
  have hmem_range : (simplexLinMap (ULift.down ∘ τ) ⇑w0.weights) ∈
      Set.range (fun (t : Convexity.StdSimplex ℝ (Fin (n + 1))) =>
        (⇑t.weights : Fin (n + 1) → ℝ)) := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      exact h_nonneg
    · simp only [Set.mem_ofPred_eq]
      exact h_sum
  obtain ⟨w', hw'⟩ := hmem_range
  refine ⟨w', ?_⟩
  apply ULift.down_injective
  change (ULift.up (⇑w'.weights) :
    ULift.{w} (Fin (n + 1) → ℝ)).down =
    (liftedSimplexLinMap τ (ULift.up (⇑w0.weights))).down
  rw [ULift.down_up, hmap_down]
  exact hw'

/-- The affine map of lifted standard simplices determined by a tuple of vertices. -/
noncomputable def liftedSimplexTopMap {n k : ℕ}
    (τ : Fin (k + 1) → ULift.{w} (Fin (n + 1) → ℝ))
    (hτ : ∀ i, τ i ∈ liftedStdSimplex.{w} n) :
    TopCat.of (liftedStdSimplex.{w} k) ⟶
      TopCat.of (liftedStdSimplex.{w} n) :=
  affineTopIn (liftedStdSimplex.{w} k) (liftedStdSimplex.{w} n)
    (liftedSimplexLinMap τ) (liftedSimplexLinMap_mem hτ)

lemma liftedStdSimplexTopHom_comp_toSSetTopHom_realizeIn
    {n k : ℕ}
    (τ : Fin (k + 1) → ULift.{w} (Fin (n + 1) → ℝ))
    (hτ : ∀ i, τ i ∈ liftedStdSimplex.{w} n) :
    liftedStdSimplexTopHom.{w} k ≫
        TopCat.toSSetTopHom (TopCat.of (liftedStdSimplex.{w} n))
          (Opposite.op (SimplexCategory.mk k))
          ((realizeInNatTrans (liftedStdSimplex.{w} n)
            (convex_liftedStdSimplex.{w} n)).app
              (Opposite.op (SimplexCategory.mk k)) ⟨τ, hτ⟩) =
      liftedSimplexTopMap τ hτ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨xval, hx⟩ := x
  obtain ⟨wx, rfl⟩ := hx
  change affineRealize τ wx = liftedSimplexLinMap τ (ULift.up (⇑wx.weights))
  apply ULift.down_injective
  rw [liftedSimplexLinMap_down, affineRealize_apply, simplexLinMap_apply]
  have h_weights_fun : (fun i => wx.weights i) =
      (ULift.up (⇑wx.weights) :
        ULift.{w} (Fin (k + 1) → ℝ)).down := by
    funext i
    rfl
  change (ULift.moduleEquiv :
    ULift.{w} (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ)).toLinearMap
      (∑ i, wx.weights i • τ i) =
      ∑ i, (ULift.up (⇑wx.weights) :
        ULift.{w} (Fin (k + 1) → ℝ)).down i • (ULift.down ∘ τ) i
  have h_mod : ∀ y : ULift.{w} (Fin (n + 1) → ℝ),
      (ULift.moduleEquiv :
        ULift.{w} (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ)).toLinearMap y =
        y.down := fun y => rfl
  rw [map_sum]
  simp only [map_smul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h_i : wx.weights i = ((ULift.up (⇑wx.weights) :
      ULift.{w} (Fin (k + 1) → ℝ)).down) i := congrFun h_weights_fun i
  rw [h_mod, Function.comp_apply, h_i]

end AlgebraicTopology
