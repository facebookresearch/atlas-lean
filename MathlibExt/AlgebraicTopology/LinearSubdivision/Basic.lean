/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LinearSimplex
public import MathlibExt.AlgebraicTopology.LinearChains

/-!
# Barycentric subdivision for linear chains

Coefficient-generic subdivision operator and prism homotopy for the linear
chain complex `LC_*(V; R)` with arbitrary preadditive target.


-/

@[expose] public section

open scoped BigOperators
open CategoryTheory Simplicial SimplexCategory SimplicialObject Matrix Limits Opposite

namespace AlgebraicTopology

universe u v w

lemma linearChainComplex_d {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (V : Type w) (n : ℕ) :
    (linearChainComplex (C := C) R V).d (n + 1) n
      = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (freemod (C := C) R V).δ i :=
  AlternatingFaceMapComplex.obj_d_eq (freemod (C := C) R V) n

noncomputable def subdivision {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] (n : ℕ) :
    (freemod (C := C) R V).obj (Opposite.op ⦋n⦌) ⟶
      (freemod (C := C) R V).obj (Opposite.op ⦋n⦌) := by
  induction n with
  | zero => exact 𝟙 _
  | succ m ih =>
    exact Sigma.desc fun σ : Fin (m + 2) → V =>
      Sigma.ι (fun _ : Fin (m + 2) → V => R) σ
        ≫ ((linearChainComplex (C := C) R V).d (m + 1) m :
            (freemod (C := C) R V).obj (Opposite.op ⦋m + 1⦌) ⟶
              (freemod (C := C) R V).obj (Opposite.op ⦋m⦌))
          ≫ ih ≫ coneMap (C := C) R V (linSimplexBarycenter σ) m

@[simp]
lemma subdivision_zero {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] :
    subdivision (C := C) R V 0 = 𝟙 _ := rfl

lemma subdivision_succ {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] (m : ℕ) :
    subdivision (C := C) R V (m + 1) = Sigma.desc (fun σ : Fin (m + 2) → V =>
      Sigma.ι (fun _ : Fin (m + 2) → V => R) σ
        ≫ ((linearChainComplex (C := C) R V).d (m + 1) m :
            (freemod (C := C) R V).obj (Opposite.op ⦋m + 1⦌) ⟶
              (freemod (C := C) R V).obj (Opposite.op ⦋m⦌))
          ≫ subdivision (C := C) R V m
          ≫ coneMap (C := C) R V (linSimplexBarycenter σ) m) := rfl

private lemma coneMap_comp_d_aux
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R : C} {V : Type w} {b : V} (n : ℕ) :
    coneMap (C := C) R V b (n + 1) ≫ (linearChainComplex (C := C) R V).d (n + 1 + 1) (n + 1)
      = 𝟙 _ - (linearChainComplex (C := C) R V).d (n + 1) n ≫ coneMap (C := C) R V b n := by
  rw [linearChainComplex_d (C := C) (R := R) (V := V) (n + 1),
    linearChainComplex_d (C := C) (R := R) (V := V) n]
  exact coneMap_comp_sum (C := C) (R := R) (b := b) n

private lemma coneMap_zero_comp_d_aux
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R : C} {V : Type w} {b : V} :
    coneMap (C := C) R V b 0 ≫ (linearChainComplex (C := C) R V).d 1 0
      = 𝟙 _ - coneMap (C := C) R V b 0 ≫ (freemod (C := C) R V).δ 1 := by
  rw [linearChainComplex_d (C := C) (R := R) (V := V) 0, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, one_smul, pow_one, neg_one_zsmul]
  erw [Preadditive.comp_add, Preadditive.comp_neg, coneMap_comp_δ_zero (C := C)]
  abel

private lemma face_comp_coneMap_zero_δ_aux
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R : C} {V : Type w} {b : V} (i : Fin 2) :
    (freemod (C := C) R V).δ i ≫ coneMap (C := C) R V b 0 ≫ (freemod (C := C) R V).δ 1
      = (sigmaConst.obj R).map
          (TypeCat.ofHom (fun _ : Fin (1 + 1) → V => (Function.const (Fin 1) b))) := by
  rw [coneMap_comp_δ (C := C) (R := R) (b := b) 0 1]
  change (freemod (C := C) R V).δ i ≫ (sigmaConst.obj R).map _ = _
  rw [SimplicialObject.δ]
  change (sigmaConst.obj R).map ((linSSet V).map (SimplexCategory.δ i).op)
      ≫ (sigmaConst.obj R).map (TypeCat.ofHom (fun σ : (linSSet V).obj (Opposite.op ⦋0⦌) =>
          (Matrix.vecCons b σ ∘ Fin.succAbove (1 : Fin 2) :
            (linSSet V).obj (Opposite.op ⦋0⦌)))) = _
  rw [← Functor.map_comp]
  congr 1
  refine ConcreteCategory.hom_ext _ _ (fun τ => ?_)
  funext j
  fin_cases j
  change Matrix.vecCons b ((linSSet V).map (SimplexCategory.δ i).op τ)
      (Fin.succAbove (1 : Fin 2) 0) = b
  rfl

private lemma d_comp_coneMap_zero_δ_aux
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R : C} {V : Type w} {b : V} :
    (linearChainComplex (C := C) R V).d 1 0 ≫ coneMap (C := C) R V b 0 ≫
      (freemod (C := C) R V).δ 1 = 0 := by
  rw [linearChainComplex_d (C := C) (R := R) (V := V) 0, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, one_smul, pow_one, neg_one_zsmul]
  erw [Preadditive.add_comp, Preadditive.neg_comp,
    face_comp_coneMap_zero_δ_aux (C := C) (R := R) (b := b) (i := 0),
    face_comp_coneMap_zero_δ_aux (C := C) (R := R) (b := b) (i := 1)]
  abel

noncomputable def freeBoundary {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (V : Type w) (n : ℕ) :
    (freemod (C := C) R V).obj (Opposite.op ⦋n + 1⦌) ⟶
      (freemod (C := C) R V).obj (Opposite.op ⦋n⦌) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (freemod (C := C) R V).δ i

lemma freeBoundary_eq_d {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (V : Type w) (n : ℕ) :
    freeBoundary (C := C) R V n = (linearChainComplex (C := C) R V).d (n + 1) n :=
  (linearChainComplex_d (C := C) R V n).symm

lemma freeBoundary_comp_freeBoundary {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (V : Type w) (n : ℕ) :
    freeBoundary (C := C) R V (n + 1) ≫ freeBoundary (C := C) R V n = 0 := by
  rw [freeBoundary_eq_d (C := C) R V (n + 1), freeBoundary_eq_d (C := C) R V n]
  exact HomologicalComplex.d_comp_d _ _ _ _

lemma coneMap_comp_freeBoundary {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (V : Type w) (b : V) (n : ℕ) :
    coneMap (C := C) R V b (n + 1) ≫ freeBoundary (C := C) R V (n + 1)
      = 𝟙 _ - freeBoundary (C := C) R V n ≫ coneMap (C := C) R V b n := by
  rw [freeBoundary_eq_d (C := C) R V (n + 1), freeBoundary_eq_d (C := C) R V n]
  exact coneMap_comp_d_aux (C := C) n

lemma subdivision_succ' {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] (m : ℕ) :
    subdivision (C := C) R V (m + 1) = Sigma.desc (fun σ : Fin (m + 2) → V =>
      Sigma.ι (fun _ : Fin (m + 2) → V => R) σ
        ≫ freeBoundary (C := C) R V m ≫ subdivision (C := C) R V m
          ≫ coneMap (C := C) R V (linSimplexBarycenter σ) m) := by
  simp_rw [freeBoundary_eq_d (C := C) (R := R) (V := V)]
  exact subdivision_succ (C := C) R V m

/-- The `σ`-component of `subdivision` in degree `m + 1` is the composite of the
corresponding boundary map, `subdivision` in degree `m`, and the barycentric cone. -/
lemma sigma_ι_comp_subdivision_succ_assoc {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] (m : ℕ)
    (σ : Fin (m + 2) → V) {X : C}
    (f : (freemod (C := C) R V).obj (Opposite.op ⦋m + 1⦌) ⟶ X) :
    Sigma.ι (fun _ : Fin (m + 2) → V => (R : C)) σ ≫ subdivision (C := C) R V (m + 1) ≫ f =
      (Sigma.ι (fun _ : Fin (m + 2) → V => (R : C)) σ ≫ freeBoundary (C := C) R V m ≫
        subdivision (C := C) R V m ≫ coneMap (C := C) R V (linSimplexBarycenter σ) m) ≫ f := by
  rw [subdivision_succ' (C := C) (R := R) (V := V) (m := m), Sigma.ι_comp_desc_assoc]

private lemma subdivision_comp_freeBoundary_aux {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] (n : ℕ) :
    subdivision (C := C) R V (n + 1) ≫ freeBoundary (C := C) R V n =
      freeBoundary (C := C) R V n ≫ subdivision (C := C) R V n := by
  induction n with
  | zero =>
    apply Sigma.hom_ext
    intro (σ : Fin 2 → V)
    let f := freeBoundary (C := C) R V 0
    let c := coneMap (C := C) R V (linSimplexBarycenter σ) 0
    let q := (freemod (C := C) R V).δ (1 : Fin 2)
    have hc : c ≫ f = 𝟙 _ - c ≫ q := by
      have h := coneMap_zero_comp_d_aux (C := C) (R := R) (b := linSimplexBarycenter σ)
      rwa [← freeBoundary_eq_d (C := C) R V 0] at h
    have hz : f ≫ c ≫ q = 0 := by
      have h := d_comp_coneMap_zero_δ_aux (C := C) (R := R) (b := linSimplexBarycenter σ)
      rwa [← freeBoundary_eq_d (C := C) R V 0] at h
    have hbridge : (f ≫ c) ≫ f = f ≫ (𝟙 _ - c ≫ q) := calc
      (f ≫ c) ≫ f = f ≫ (c ≫ f) := Category.assoc _ _ _
      _ = f ≫ (𝟙 _ - c ≫ q) := congrArg (fun t => f ≫ t) hc
    erw [sigma_ι_comp_subdivision_succ_assoc (C := C) R V 0 σ]
    erw [subdivision_zero (C := C) R V, Category.id_comp]
    erw [Category.assoc, hbridge]
    simp only [Preadditive.comp_sub, Category.comp_id]
    rw [hz, sub_zero]
    rfl
  | succ k ih =>
    apply Sigma.hom_ext
    intro (σ : Fin (k + 3) → V)
    let f := freeBoundary (C := C) R V (k + 1)
    let s := subdivision (C := C) R V (k + 1)
    let c := coneMap (C := C) R V (linSimplexBarycenter σ) (k + 1)
    let g := freeBoundary (C := C) R V k
    let c' := coneMap (C := C) R V (linSimplexBarycenter σ) k
    have hc : c ≫ f = 𝟙 _ - g ≫ c' :=
      coneMap_comp_freeBoundary (C := C) R V (linSimplexBarycenter σ) k
    have hbridge : (f ≫ s ≫ c) ≫ f = f ≫ s ≫ (𝟙 _ - g ≫ c') := calc
      (f ≫ s ≫ c) ≫ f = f ≫ s ≫ (c ≫ f) := by simp only [Category.assoc]
      _ = f ≫ s ≫ (𝟙 _ - g ≫ c') := congrArg (fun t => f ≫ s ≫ t) hc
    have hz : f ≫ s ≫ g ≫ c' = 0 := by
      have hfg : f ≫ g = 0 := freeBoundary_comp_freeBoundary (C := C) R V k
      calc f ≫ s ≫ g ≫ c' = f ≫ (s ≫ g) ≫ c' := by simp only [Category.assoc]
        _ = f ≫ (g ≫ subdivision (C := C) R V k) ≫ c' := by rw [ih]
        _ = (f ≫ g) ≫ subdivision (C := C) R V k ≫ c' := by simp only [Category.assoc]
        _ = 0 := by simp only [hfg, Limits.zero_comp]
    erw [sigma_ι_comp_subdivision_succ_assoc (C := C) R V (k + 1) σ]
    erw [Category.assoc, hbridge]
    simp only [Preadditive.comp_sub, Category.comp_id]
    rw [hz, sub_zero]
    rfl

/-- Linear subdivision commutes with the free boundary operator. -/
theorem subdivision_comp_freeBoundary {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] (n : ℕ) :
    subdivision (C := C) R V (n + 1) ≫ freeBoundary (C := C) R V n =
      freeBoundary (C := C) R V n ≫ subdivision (C := C) R V n :=
  subdivision_comp_freeBoundary_aux (C := C) R V n

theorem subdivision_comp_d {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] (n : ℕ) :
    subdivision (C := C) R V (n + 1) ≫ (linearChainComplex (C := C) R V).d (n + 1) n =
      (linearChainComplex (C := C) R V).d (n + 1) n ≫ subdivision (C := C) R V n := by
  simp only [← freeBoundary_eq_d (C := C) R V n]
  exact subdivision_comp_freeBoundary_aux (C := C) R V n

@[reassoc]
lemma subdivision_naturality
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {V W : Type w} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W) (n : ℕ) :
    subdivision (C := C) R V n ≫
        ((linearChainComplexFunctor R).map (TypeCat.ofHom L)).f n =
      ((linearChainComplexFunctor R).map (TypeCat.ofHom L)).f n ≫
        subdivision (C := C) R W n := by
  let Φ : linearChainComplex (C := C) R V ⟶ linearChainComplex (C := C) R W :=
    (linearChainComplexFunctor R).map (TypeCat.ofHom L)
  let sV : ∀ k : ℕ, (linearChainComplex (C := C) R V).X k ⟶
      (linearChainComplex (C := C) R V).X k :=
    fun k => subdivision (C := C) R V k
  let sW : ∀ k : ℕ, (linearChainComplex (C := C) R W).X k ⟶
      (linearChainComplex (C := C) R W).X k :=
    fun k => subdivision (C := C) R W k
  change sV n ≫ Φ.f n = Φ.f n ≫ sW n
  induction n with
  | zero =>
      dsimp only [sV, sW]
      rw [subdivision_zero, subdivision_zero]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ m ih =>
      apply SSet.chainComplex_hom_ext
      intro σ
      let τ : Fin (m + 2) → V := σ
      let cV : (linearChainComplex (C := C) R V).X m ⟶
          (linearChainComplex (C := C) R V).X (m + 1) :=
        coneMap (C := C) R V (linSimplexBarycenter τ) m
      let cW : (linearChainComplex (C := C) R W).X m ⟶
          (linearChainComplex (C := C) R W).X (m + 1) :=
        coneMap (C := C) R W (L (linSimplexBarycenter τ)) m
      let cW' : (linearChainComplex (C := C) R W).X m ⟶
          (linearChainComplex (C := C) R W).X (m + 1) :=
        coneMap (C := C) R W (linSimplexBarycenter (L ∘ τ)) m
      have hsub : SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
            sV (m + 1) =
          SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
            (linearChainComplex (C := C) R V).d (m + 1) m ≫
              sV m ≫ cV := by
        dsimp only [sV, cV]
        unfold SSet.ιChainComplex
        rw [subdivision_succ]
        erw [Sigma.ι_comp_desc]
        rfl
      have hsubW : SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) ≫
            sW (m + 1) =
          SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) ≫
            (linearChainComplex (C := C) R W).d (m + 1) m ≫
              sW m ≫ cW' := by
        dsimp only [sW, cW']
        unfold SSet.ιChainComplex
        rw [subdivision_succ]
        erw [Sigma.ι_comp_desc]
        rfl
      have hdiff : (linearChainComplex (C := C) R V).d (m + 1) m ≫ Φ.f m =
          Φ.f (m + 1) ≫ (linearChainComplex (C := C) R W).d (m + 1) m := by
        exact (Φ.comm (m + 1) m).symm
      have hcone : cV ≫ Φ.f (m + 1) = Φ.f m ≫ cW := by
        dsimp only [cV, cW, Φ]
        exact coneMap_naturality L (linSimplexBarycenter τ) m
      have hι : SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ Φ.f (m + 1) =
          SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) := by
        dsimp only [Φ]
        dsimp only [τ]
        exact linearChainComplexFunctor_map_ι R L σ
      have hbary : cW = cW' := by
        dsimp only [cW, cW']
        exact congrArg (fun b => coneMap (C := C) R W b m)
          (linSimplexBarycenter_comp_linear L τ).symm
      calc
        SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              sV (m + 1) ≫ Φ.f (m + 1) =
            (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              sV (m + 1)) ≫ Φ.f (m + 1) := by
          exact (Category.assoc _ _ _).symm
        _ = (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              (linearChainComplex (C := C) R V).d (m + 1) m ≫
                sV m ≫ cV) ≫ Φ.f (m + 1) := by
          exact congrArg (· ≫ Φ.f (m + 1)) hsub
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              (linearChainComplex (C := C) R V).d (m + 1) m ≫
                sV m ≫ (Φ.f m ≫ cW) := by
          simp only [Category.assoc]
          rw [hcone]
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              (linearChainComplex (C := C) R V).d (m + 1) m ≫
                (Φ.f m ≫ sW m) ≫ cW := by
          simp only [Category.assoc]
          erw [reassoc_of% ih]
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              (Φ.f (m + 1) ≫ (linearChainComplex (C := C) R W).d (m + 1) m) ≫
                sW m ≫ cW := by
          simp only [Category.assoc]
          erw [reassoc_of% hdiff]
        _ = SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) ≫
              (linearChainComplex (C := C) R W).d (m + 1) m ≫
                sW m ≫ cW' := by
          rw [← hbary]
          simp only [Category.assoc]
          erw [reassoc_of% hι]
        _ = SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) ≫
              sW (m + 1) := hsubW.symm
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              Φ.f (m + 1) ≫ sW (m + 1) := by
          erw [reassoc_of% hι]

noncomputable def linearSubdivisionHom {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] :
    linearChainComplex (C := C) R V ⟶ linearChainComplex (C := C) R V where
  f n := subdivision (C := C) R V n
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    exact subdivision_comp_d (C := C) R V _

@[simp]
lemma linearSubdivisionHom_f_component {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] (n : ℕ) :
    (linearSubdivisionHom (C := C) R V).f n = subdivision (C := C) R V n := rfl

noncomputable def homotopyOp {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] (n : ℕ) :
    (freemod (C := C) R V).obj (Opposite.op ⦋n⦌) ⟶
      (freemod (C := C) R V).obj (Opposite.op ⦋n + 1⦌) := by
  induction n with
  | zero =>
    exact Sigma.desc fun lam : Fin 1 → V =>
      Sigma.ι (fun _ : Fin 1 → V => R) lam
        ≫ coneMap (C := C) R V (linSimplexBarycenter lam) 0
  | succ m ih =>
    exact Sigma.desc fun lam : Fin (m + 2) → V =>
      Sigma.ι (fun _ : Fin (m + 2) → V => R) lam
        ≫ (𝟙 _ - ((linearChainComplex (C := C) R V).d (m + 1) m :
            (freemod (C := C) R V).obj (Opposite.op ⦋m + 1⦌) ⟶
              (freemod (C := C) R V).obj (Opposite.op ⦋m⦌)) ≫ ih)
          ≫ coneMap (C := C) R V (linSimplexBarycenter lam) (m + 1)

@[simp]
lemma homotopyOp_zero {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] :
    homotopyOp (C := C) R V 0 = Sigma.desc (fun lam : Fin 1 → V =>
      Sigma.ι (fun _ : Fin 1 → V => R) lam
        ≫ coneMap (C := C) R V (linSimplexBarycenter lam) 0) := rfl

lemma homotopyOp_succ {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] (m : ℕ) :
    homotopyOp (C := C) R V (m + 1) = Sigma.desc (fun lam : Fin (m + 2) → V =>
      Sigma.ι (fun _ : Fin (m + 2) → V => R) lam
        ≫ (𝟙 _ - ((linearChainComplex (C := C) R V).d (m + 1) m :
            (freemod (C := C) R V).obj (Opposite.op ⦋m + 1⦌) ⟶
              (freemod (C := C) R V).obj (Opposite.op ⦋m⦌)) ≫ homotopyOp (C := C) R V m)
          ≫ coneMap (C := C) R V (linSimplexBarycenter lam) (m + 1)) := rfl

lemma homotopyOp_succ' {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] (m : ℕ) :
    homotopyOp (C := C) R V (m + 1) = Sigma.desc (fun lam : Fin (m + 2) → V =>
      Sigma.ι (fun _ : Fin (m + 2) → V => R) lam
        ≫ (𝟙 _ - freeBoundary (C := C) R V m ≫ homotopyOp (C := C) R V m)
          ≫ coneMap (C := C) R V (linSimplexBarycenter lam) (m + 1)) := by
  simp_rw [freeBoundary_eq_d (C := C) (R := R) (V := V)]
  exact homotopyOp_succ (C := C) R V m

@[reassoc]
lemma homotopyOp_naturality
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {V W : Type w} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W) (n : ℕ) :
    homotopyOp (C := C) R V n ≫
        ((linearChainComplexFunctor R).map (TypeCat.ofHom L)).f (n + 1) =
      ((linearChainComplexFunctor R).map (TypeCat.ofHom L)).f n ≫
        homotopyOp (C := C) R W n := by
  let Φ : linearChainComplex (C := C) R V ⟶ linearChainComplex (C := C) R W :=
    (linearChainComplexFunctor R).map (TypeCat.ofHom L)
  let tV : ∀ k : ℕ, (linearChainComplex (C := C) R V).X k ⟶
      (linearChainComplex (C := C) R V).X (k + 1) :=
    fun k => homotopyOp (C := C) R V k
  let tW : ∀ k : ℕ, (linearChainComplex (C := C) R W).X k ⟶
      (linearChainComplex (C := C) R W).X (k + 1) :=
    fun k => homotopyOp (C := C) R W k
  change tV n ≫ Φ.f (n + 1) = Φ.f n ≫ tW n
  induction n with
  | zero =>
      apply SSet.chainComplex_hom_ext
      intro σ
      let τ : Fin 1 → V := σ
      let cV : (linearChainComplex (C := C) R V).X 0 ⟶
          (linearChainComplex (C := C) R V).X 1 :=
        coneMap (C := C) R V (linSimplexBarycenter τ) 0
      let cW : (linearChainComplex (C := C) R W).X 0 ⟶
          (linearChainComplex (C := C) R W).X 1 :=
        coneMap (C := C) R W (L (linSimplexBarycenter τ)) 0
      let cW' : (linearChainComplex (C := C) R W).X 0 ⟶
          (linearChainComplex (C := C) R W).X 1 :=
        coneMap (C := C) R W (linSimplexBarycenter (L ∘ τ)) 0
      have hzeroV : SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ tV 0 =
          SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ cV := by
        dsimp only [tV, cV]
        unfold SSet.ιChainComplex
        rw [homotopyOp_zero]
        erw [Sigma.ι_comp_desc]
        rfl
      have hzeroW : SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) ≫ tW 0 =
          SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) ≫ cW' := by
        dsimp only [tW, cW']
        unfold SSet.ιChainComplex
        rw [homotopyOp_zero]
        erw [Sigma.ι_comp_desc]
        rfl
      have hcone : cV ≫ Φ.f 1 = Φ.f 0 ≫ cW := by
        dsimp only [cV, cW, Φ]
        exact coneMap_naturality L (linSimplexBarycenter τ) 0
      have hι : SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ Φ.f 0 =
          SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) := by
        dsimp only [Φ, τ]
        exact linearChainComplexFunctor_map_ι R L σ
      have hbary : cW = cW' := by
        dsimp only [cW, cW']
        exact congrArg (fun b => coneMap (C := C) R W b 0)
          (linSimplexBarycenter_comp_linear L τ).symm
      calc
        SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ tV 0 ≫ Φ.f 1 =
            (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ tV 0) ≫ Φ.f 1 := by
          exact (Category.assoc _ _ _).symm
        _ = (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ cV) ≫ Φ.f 1 := by
          exact congrArg (· ≫ Φ.f 1) hzeroV
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ (Φ.f 0 ≫ cW) := by
          simp only [Category.assoc]
          rw [hcone]
        _ = SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) ≫ cW' := by
          rw [← hbary]
          erw [reassoc_of% hι]
        _ = SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) ≫ tW 0 :=
          hzeroW.symm
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ Φ.f 0 ≫ tW 0 := by
          erw [reassoc_of% hι]
  | succ m ih =>
      apply SSet.chainComplex_hom_ext
      intro σ
      let τ : Fin (m + 2) → V := σ
      let cV : (linearChainComplex (C := C) R V).X (m + 1) ⟶
          (linearChainComplex (C := C) R V).X (m + 2) :=
        coneMap (C := C) R V (linSimplexBarycenter τ) (m + 1)
      let cW : (linearChainComplex (C := C) R W).X (m + 1) ⟶
          (linearChainComplex (C := C) R W).X (m + 2) :=
        coneMap (C := C) R W (L (linSimplexBarycenter τ)) (m + 1)
      let cW' : (linearChainComplex (C := C) R W).X (m + 1) ⟶
          (linearChainComplex (C := C) R W).X (m + 2) :=
        coneMap (C := C) R W (linSimplexBarycenter (L ∘ τ)) (m + 1)
      let qV : (linearChainComplex (C := C) R V).X (m + 1) ⟶
          (linearChainComplex (C := C) R V).X (m + 1) :=
        𝟙 _ - (linearChainComplex (C := C) R V).d (m + 1) m ≫ tV m
      let qW : (linearChainComplex (C := C) R W).X (m + 1) ⟶
          (linearChainComplex (C := C) R W).X (m + 1) :=
        𝟙 _ - (linearChainComplex (C := C) R W).d (m + 1) m ≫ tW m
      have hsuccV : SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ tV (m + 1) =
          SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ qV ≫ cV := by
        dsimp only [tV, qV, cV]
        unfold SSet.ιChainComplex
        rw [homotopyOp_succ]
        erw [Sigma.ι_comp_desc]
        rfl
      have hsuccW : SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) ≫
            tW (m + 1) =
          SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) ≫ qW ≫ cW' := by
        dsimp only [tW, qW, cW']
        unfold SSet.ιChainComplex
        rw [homotopyOp_succ]
        erw [Sigma.ι_comp_desc]
        rfl
      have hdiff : (linearChainComplex (C := C) R V).d (m + 1) m ≫ Φ.f m =
          Φ.f (m + 1) ≫ (linearChainComplex (C := C) R W).d (m + 1) m := by
        exact (Φ.comm (m + 1) m).symm
      have hq : qV ≫ Φ.f (m + 1) = Φ.f (m + 1) ≫ qW := by
        dsimp only [qV, qW]
        simp only [Preadditive.sub_comp, Preadditive.comp_sub,
          Category.id_comp, Category.comp_id, Category.assoc]
        rw [ih]
        erw [reassoc_of% hdiff]
      have hcone : cV ≫ Φ.f (m + 2) = Φ.f (m + 1) ≫ cW := by
        dsimp only [cV, cW, Φ]
        exact coneMap_naturality L (linSimplexBarycenter τ) (m + 1)
      have hι : SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ Φ.f (m + 1) =
          SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) := by
        dsimp only [Φ, τ]
        exact linearChainComplexFunctor_map_ι R L σ
      have hbary : cW = cW' := by
        dsimp only [cW, cW']
        exact congrArg (fun b => coneMap (C := C) R W b (m + 1))
          (linSimplexBarycenter_comp_linear L τ).symm
      calc
        SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              tV (m + 1) ≫ Φ.f (m + 2) =
            (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              tV (m + 1)) ≫ Φ.f (m + 2) := by
          exact (Category.assoc _ _ _).symm
        _ = (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ qV ≫ cV) ≫
              Φ.f (m + 2) := by
          exact congrArg (· ≫ Φ.f (m + 2)) hsuccV
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              qV ≫ (Φ.f (m + 1) ≫ cW) := by
          simp only [Category.assoc]
          rw [hcone]
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              (Φ.f (m + 1) ≫ qW) ≫ cW := by
          erw [reassoc_of% hq]
          simp only [Category.assoc]
        _ = SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) ≫
              qW ≫ cW' := by
          rw [← hbary]
          simp only [Category.assoc]
          erw [reassoc_of% hι]
        _ = SSet.ιChainComplex (X := linSSet W) (R := R) (L ∘ τ) ≫
              tW (m + 1) := hsuccW.symm
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              Φ.f (m + 1) ≫ tW (m + 1) := by
          erw [reassoc_of% hι]

private lemma homotopyOp_zero_face_local
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V]
    (lam : Fin 1 → V) :
    Sigma.ι (fun _ : Fin 1 → V => (R : C)) lam
        ≫ coneMap (C := C) R V (linSimplexBarycenter lam) 0 ≫
          (freemod (C := C) R V).δ 1
      = Sigma.ι (fun _ : Fin 1 → V => (R : C)) lam := by
  have hfun : (Matrix.vecCons (linSimplexBarycenter lam) lam ∘ Fin.succAbove (1 : Fin 2)) =
      lam := by
    ext j
    have hj : j = (0 : Fin 1) := by
      have : Subsingleton (Fin 1) := inferInstance
      exact Subsingleton.elim _ _
    rw [hj]
    simp only [Function.comp_apply]
    have h1 : Fin.succAbove (1 : Fin 2) (0 : Fin 1) = (0 : Fin 2) := rfl
    simp only [h1, Matrix.cons_val_zero, linSimplexBarycenter_point]
  have h1 : (Sigma.ι (fun _ : Fin 1 → V => (R : C)) lam ≫
        coneMap (C := C) R V (linSimplexBarycenter lam) 0) ≫
          (freemod (C := C) R V).δ 1
      = Sigma.ι (fun _ : Fin 2 → V => (R : C)) (Matrix.vecCons (linSimplexBarycenter lam) lam)
          ≫ (freemod (C := C) R V).δ 1 :=
    sigma_ι_comp_coneMap_assoc (C := C) (R := R) (b := linSimplexBarycenter lam)
      (tau := lam) ((freemod (C := C) R V).δ 1)
  have h2 : Sigma.ι (fun _ : Fin 2 → V => (R : C))
        (Matrix.vecCons (linSimplexBarycenter lam) lam) ≫ (freemod (C := C) R V).δ 1
      = Sigma.ι (fun _ : Fin 1 → V => (R : C))
          (Matrix.vecCons (linSimplexBarycenter lam) lam ∘ Fin.succAbove (1 : Fin 2)) :=
    sigma_ι_comp_freemod_δ (C := C) (R := R)
      (tau := Matrix.vecCons (linSimplexBarycenter lam) lam) (i := 1)
  have h3 : Sigma.ι (fun _ : Fin 1 → V => (R : C))
        (Matrix.vecCons (linSimplexBarycenter lam) lam ∘ Fin.succAbove (1 : Fin 2)) =
      Sigma.ι (fun _ : Fin 1 → V => (R : C)) lam :=
    congrArg (fun t : Fin 1 → V => Sigma.ι (fun _ : Fin 1 → V => (R : C)) t) hfun
  have h_left : (Sigma.ι (fun _ : Fin 1 → V => (R : C)) lam ≫
        coneMap (C := C) R V (linSimplexBarycenter lam) 0) ≫
          (freemod (C := C) R V).δ 1
      = Sigma.ι (fun _ : Fin 1 → V => (R : C)) lam := by
    rw [h1, h2, h3]
  have h_assoc : Sigma.ι (fun _ : Fin 1 → V => (R : C)) lam ≫
        coneMap (C := C) R V (linSimplexBarycenter lam) 0 ≫ (freemod (C := C) R V).δ 1
      = (Sigma.ι (fun _ : Fin 1 → V => (R : C)) lam ≫
          coneMap (C := C) R V (linSimplexBarycenter lam) 0) ≫ (freemod (C := C) R V).δ 1 :=
    (Category.assoc _ _ _).symm
  rw [h_assoc]
  exact h_left

theorem homotopyOp_zero_comp_d_local
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] :
    homotopyOp (C := C) R V 0 ≫ (linearChainComplex (C := C) R V).d 1 0 =
      𝟙 _ - subdivision (C := C) R V 0 := by
  rw [subdivision_zero (C := C) (R := R) (V := V), homotopyOp_zero (C := C) (R := R) (V := V)]
  refine Sigma.hom_ext _ _ (fun lam => ?_)
  erw [Sigma.ι_comp_desc_assoc]
  erw [Category.assoc]
  erw [coneMap_zero_comp_d_aux (C := C) (R := R) (b := linSimplexBarycenter lam),
    Preadditive.comp_sub, Category.comp_id,
    homotopyOp_zero_face_local (C := C) (R := R) (V := V) (lam := lam),
    Preadditive.comp_sub, Category.comp_id]
  rfl

private lemma homotopyOp_homotopy_of_local
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] (n : ℕ)
    (hdTd : freeBoundary (C := C) R V n ≫ homotopyOp (C := C) R V n ≫
        freeBoundary (C := C) R V n =
        freeBoundary (C := C) R V n ≫ (𝟙 _ - subdivision (C := C) R V n)) :
    homotopyOp (C := C) R V (n + 1) ≫ freeBoundary (C := C) R V (n + 1) +
        freeBoundary (C := C) R V n ≫ homotopyOp (C := C) R V n =
      𝟙 _ - subdivision (C := C) R V (n + 1) := by
  rw [homotopyOp_succ' (C := C) R V n, subdivision_succ' (C := C) R V n]
  refine Sigma.hom_ext _ _ (fun lam => ?_)
  erw [Preadditive.comp_add, Sigma.ι_comp_desc_assoc, Preadditive.comp_sub, Category.comp_id,
    Sigma.ι_comp_desc]
  rw [Category.assoc, Category.assoc,
    coneMap_comp_freeBoundary (C := C) R V (linSimplexBarycenter lam) n]
  erw [← Preadditive.comp_add]
  have hAB : (freeBoundary (C := C) R V n ≫ homotopyOp (C := C) R V n) ≫
        (freeBoundary (C := C) R V n ≫ coneMap (C := C) R V (linSimplexBarycenter lam) n) =
      freeBoundary (C := C) R V n ≫ coneMap (C := C) R V (linSimplexBarycenter lam) n -
        freeBoundary (C := C) R V n ≫ subdivision (C := C) R V n ≫
          coneMap (C := C) R V (linSimplexBarycenter lam) n := by
    rw [← Category.assoc (freeBoundary (C := C) R V n ≫ homotopyOp (C := C) R V n)
        (freeBoundary (C := C) R V n) (coneMap (C := C) R V (linSimplexBarycenter lam) n),
      Category.assoc (freeBoundary (C := C) R V n) (homotopyOp (C := C) R V n)
        (freeBoundary (C := C) R V n), hdTd, Category.assoc, Preadditive.sub_comp,
      Category.id_comp, Preadditive.comp_sub]
  have key : (𝟙 _ - freeBoundary (C := C) R V n ≫ homotopyOp (C := C) R V n) ≫
        (𝟙 _ - freeBoundary (C := C) R V n ≫ coneMap (C := C) R V (linSimplexBarycenter lam) n) +
        freeBoundary (C := C) R V n ≫ homotopyOp (C := C) R V n =
      𝟙 _ - freeBoundary (C := C) R V n ≫ subdivision (C := C) R V n ≫
          coneMap (C := C) R V (linSimplexBarycenter lam) n := by
    rw [Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub, Category.comp_id, hAB]
    abel
  erw [key, Preadditive.comp_sub, Category.comp_id]
  rfl

theorem homotopyOp_homotopy_local
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] (n : ℕ) :
    homotopyOp (C := C) R V (n + 1) ≫ freeBoundary (C := C) R V (n + 1) +
        freeBoundary (C := C) R V n ≫ homotopyOp (C := C) R V n =
      𝟙 _ - subdivision (C := C) R V (n + 1) := by
  induction n with
  | zero =>
    have hT0 : homotopyOp (C := C) R V 0 ≫ freeBoundary (C := C) R V 0 =
        𝟙 _ - subdivision (C := C) R V 0 := by
      rw [freeBoundary_eq_d (C := C) R V 0]
      exact homotopyOp_zero_comp_d_local (C := C) R V
    have hdTd : freeBoundary (C := C) R V 0 ≫ homotopyOp (C := C) R V 0 ≫
        freeBoundary (C := C) R V 0 =
        freeBoundary (C := C) R V 0 ≫ (𝟙 _ - subdivision (C := C) R V 0) := by
      calc freeBoundary (C := C) R V 0 ≫ homotopyOp (C := C) R V 0 ≫
            freeBoundary (C := C) R V 0
          = freeBoundary (C := C) R V 0 ≫
              (homotopyOp (C := C) R V 0 ≫ freeBoundary (C := C) R V 0) := rfl
        _ = freeBoundary (C := C) R V 0 ≫ (𝟙 _ - subdivision (C := C) R V 0) := by rw [hT0]
    exact homotopyOp_homotopy_of_local (C := C) R V 0 hdTd
  | succ m ih =>
    have hTd : homotopyOp (C := C) R V (m + 1) ≫ freeBoundary (C := C) R V (m + 1) =
        𝟙 _ - subdivision (C := C) R V (m + 1) -
          freeBoundary (C := C) R V m ≫ homotopyOp (C := C) R V m :=
      eq_sub_of_add_eq ih
    have hdTd : freeBoundary (C := C) R V (m + 1) ≫ homotopyOp (C := C) R V (m + 1) ≫
        freeBoundary (C := C) R V (m + 1) =
        freeBoundary (C := C) R V (m + 1) ≫ (𝟙 _ - subdivision (C := C) R V (m + 1)) := by
      calc freeBoundary (C := C) R V (m + 1) ≫ homotopyOp (C := C) R V (m + 1) ≫
            freeBoundary (C := C) R V (m + 1)
          = freeBoundary (C := C) R V (m + 1) ≫
              (homotopyOp (C := C) R V (m + 1) ≫ freeBoundary (C := C) R V (m + 1)) := rfl
        _ = freeBoundary (C := C) R V (m + 1) ≫
              (𝟙 _ - subdivision (C := C) R V (m + 1) -
                freeBoundary (C := C) R V m ≫ homotopyOp (C := C) R V m) := by rw [hTd]
        _ = freeBoundary (C := C) R V (m + 1) ≫ (𝟙 _ - subdivision (C := C) R V (m + 1)) -
              freeBoundary (C := C) R V (m + 1) ≫ freeBoundary (C := C) R V m ≫
                homotopyOp (C := C) R V m := by
            rw [Preadditive.comp_sub, Preadditive.comp_sub]
        _ = freeBoundary (C := C) R V (m + 1) ≫ (𝟙 _ - subdivision (C := C) R V (m + 1)) -
              (freeBoundary (C := C) R V (m + 1) ≫ freeBoundary (C := C) R V m) ≫
                homotopyOp (C := C) R V m := by
            rw [Category.assoc]
        _ = freeBoundary (C := C) R V (m + 1) ≫ (𝟙 _ - subdivision (C := C) R V (m + 1)) -
              (0 : _ ) ≫ homotopyOp (C := C) R V m := by
            rw [freeBoundary_comp_freeBoundary (C := C) R V m]
        _ = freeBoundary (C := C) R V (m + 1) ≫ (𝟙 _ - subdivision (C := C) R V (m + 1)) := by
            rw [Limits.zero_comp, sub_zero]
    exact homotopyOp_homotopy_of_local (C := C) R V (m + 1) hdTd

/-- Chain homotopy from identity to subdivision. -/
noncomputable def linearSubdivisionHomotopy {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] :
    _root_.Homotopy (𝟙 (linearChainComplex (C := C) R V))
      (linearSubdivisionHom (C := C) R V) := by
  let fam : ∀ i j : ℕ, (linearChainComplex (C := C) R V).X i ⟶
      (linearChainComplex (C := C) R V).X j :=
    fun i j => if h : i + 1 = j then (h ▸ homotopyOp (C := C) R V i) else 0
  let sX : ∀ n, (linearChainComplex (C := C) R V).X n ⟶
      (linearChainComplex (C := C) R V).X n :=
    fun n => subdivision (C := C) R V n
  let hX : ∀ n, (linearChainComplex (C := C) R V).X n ⟶
      (linearChainComplex (C := C) R V).X (n + 1) :=
    fun n => homotopyOp (C := C) R V n
  let fX : ∀ n, (linearChainComplex (C := C) R V).X (n + 1) ⟶
      (linearChainComplex (C := C) R V).X n :=
    fun n => freeBoundary (C := C) R V n
  have fam_succ_X : ∀ n, fam n (n + 1) = hX n := by
    intro n
    simp [fam, hX]
    rfl
  have fam_zero : ∀ {i j : ℕ}, i + 1 ≠ j → fam i j = 0 := by
    intro i j h
    simp [fam, h]
  refine
    { hom := fam
      zero := by
        intro i j hij
        have hne : i + 1 ≠ j := by simpa [ComplexShape.down] using hij
        exact fam_zero hne
      comm := by
        intro i
        cases i with
        | zero =>
          have hFam : fam 0 1 = hX 0 := fam_succ_X 0
          have hD0 : dNext 0 fam = 0 := Homotopy.dNext_zero_chainComplex _
          have hP0 : prevD 0 fam = fam 0 1 ≫ (linearChainComplex (C := C) R V).d 1 0 := by
            rw [Homotopy.prevD_chainComplex]
          have hP0' : prevD 0 fam = hX 0 ≫ (linearChainComplex (C := C) R V).d 1 0 := by
            rw [hP0, hFam]
          have hH0 : hX 0 ≫ (linearChainComplex (C := C) R V).d 1 0 =
              𝟙 ((linearChainComplex (C := C) R V).X 0) - sX 0 := by
            exact homotopyOp_zero_comp_d_local (C := C) R V
          calc 𝟙 ((linearChainComplex (C := C) R V).X 0)
              = prevD 0 fam + dNext 0 fam + sX 0 := by
                rw [hD0, hP0', hH0]
                abel
            _ = dNext 0 fam + prevD 0 fam + (linearSubdivisionHom (C := C) R V).f 0 := by
                abel
        | succ n =>
          have hFamN : fam n (n + 1) = hX n := fam_succ_X n
          have hFamSn : fam (n + 1) (n + 2) = hX (n + 1) := fam_succ_X (n + 1)
          have hDn : dNext (n + 1) fam =
              (linearChainComplex (C := C) R V).d (n + 1) n ≫ fam n (n + 1) := by
            rw [Homotopy.dNext_succ_chainComplex]
          have hPn : prevD (n + 1) fam =
              fam (n + 1) (n + 2) ≫ (linearChainComplex (C := C) R V).d (n + 2) (n + 1) := by
            rw [Homotopy.prevD_chainComplex]
          have hDn' : dNext (n + 1) fam =
              (linearChainComplex (C := C) R V).d (n + 1) n ≫ hX n := by
            rw [hDn, hFamN]
          have hPn' : prevD (n + 1) fam =
              hX (n + 1) ≫ (linearChainComplex (C := C) R V).d (n + 2) (n + 1) := by
            rw [hPn, hFamSn]
          have hFreeN : (linearChainComplex (C := C) R V).d (n + 1) n = fX n :=
            (freeBoundary_eq_d (C := C) R V n).symm
          have hFreeSn : (linearChainComplex (C := C) R V).d (n + 2) (n + 1) = fX (n + 1) :=
            (freeBoundary_eq_d (C := C) R V (n + 1)).symm
          have hEq : (linearChainComplex (C := C) R V).d (n + 1) n ≫ hX n +
              hX (n + 1) ≫ (linearChainComplex (C := C) R V).d (n + 2) (n + 1) =
              𝟙 ((linearChainComplex (C := C) R V).X (n + 1)) - sX (n + 1) := by
            rw [hFreeN, hFreeSn]
            have hloc : hX (n + 1) ≫ fX (n + 1) + fX n ≫ hX n =
                𝟙 ((linearChainComplex (C := C) R V).X (n + 1)) - sX (n + 1) :=
              homotopyOp_homotopy_local (C := C) R V n
            calc (fX n ≫ hX n + hX (n + 1) ≫ fX (n + 1))
                = (hX (n + 1) ≫ fX (n + 1) + fX n ≫ hX n) := by exact add_comm _ _
              _ = 𝟙 ((linearChainComplex (C := C) R V).X (n + 1)) - sX (n + 1) := hloc
          have hComb : dNext (n + 1) fam + prevD (n + 1) fam =
              𝟙 ((linearChainComplex (C := C) R V).X (n + 1)) - sX (n + 1) := by
            rw [hDn', hPn', hEq]
          calc 𝟙 ((linearChainComplex (C := C) R V).X (n + 1))
              = dNext (n + 1) fam + prevD (n + 1) fam + sX (n + 1) := by
                rw [hComb, sub_add_cancel]
            _ = dNext (n + 1) fam + prevD (n + 1) fam +
                (linearSubdivisionHom (C := C) R V).f (n + 1) := rfl
    }

@[simp]
lemma linearSubdivisionHomotopy_succ_component {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] (n : ℕ) :
    (linearSubdivisionHomotopy (C := C) R V).hom n (n + 1) = homotopyOp (C := C) R V n := by
  simp [linearSubdivisionHomotopy]
  rfl

lemma linearSubdivisionHomotopy_eq_zero_of_ne {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (V : Type w) [AddCommGroup V] [Module ℝ V] {i j : ℕ}
    (h : i + 1 ≠ j) : (linearSubdivisionHomotopy (C := C) R V).hom i j = 0 := by
  simp [linearSubdivisionHomotopy, h]

@[reassoc]
lemma freeBoundary_naturality_coefficient
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) (V : Type w) (n : ℕ) :
    freeBoundary (C := C) R V n ≫
        (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f n =
      (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f (n + 1) ≫
        freeBoundary (C := C) S V n := by
  let Φ : linearChainComplex (C := C) R V ⟶ linearChainComplex (C := C) S V :=
    (((SSet.chainComplexFunctor C).map a).app (linSSet V))
  have h : (linearChainComplex (C := C) R V).d (n + 1) n ≫ Φ.f n =
      Φ.f (n + 1) ≫ (linearChainComplex (C := C) S V).d (n + 1) n := by
    exact (Φ.comm (n + 1) n).symm
  rw [← freeBoundary_eq_d (C := C) (R := R) (V := V) (n := n),
    ← freeBoundary_eq_d (C := C) (R := S) (V := V) (n := n)] at h
  exact h

@[reassoc]
theorem subdivision_naturality_coefficient
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) (V : Type w) [AddCommGroup V] [Module ℝ V] (n : ℕ) :
    subdivision (C := C) R V n ≫
        (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f n =
      (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f n ≫
        subdivision (C := C) S V n := by
  let Φ : linearChainComplex (C := C) R V ⟶ linearChainComplex (C := C) S V :=
    (((SSet.chainComplexFunctor C).map a).app (linSSet V))
  let sR : ∀ k : ℕ, (linearChainComplex (C := C) R V).X k ⟶
      (linearChainComplex (C := C) R V).X k :=
    fun k => subdivision (C := C) R V k
  let sS : ∀ k : ℕ, (linearChainComplex (C := C) S V).X k ⟶
      (linearChainComplex (C := C) S V).X k :=
    fun k => subdivision (C := C) S V k
  change sR n ≫ Φ.f n = Φ.f n ≫ sS n
  induction n with
  | zero =>
    dsimp only [sR, sS]
    rw [subdivision_zero, subdivision_zero]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ m ih =>
    apply SSet.chainComplex_hom_ext
    intro σ
    let τ : Fin (m + 2) → V := σ
    let cR : (linearChainComplex (C := C) R V).X m ⟶
        (linearChainComplex (C := C) R V).X (m + 1) :=
      coneMap (C := C) R V (linSimplexBarycenter τ) m
    let cS : (linearChainComplex (C := C) S V).X m ⟶
        (linearChainComplex (C := C) S V).X (m + 1) :=
      coneMap (C := C) S V (linSimplexBarycenter τ) m
    have hsub : SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ sR (m + 1) =
        SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
          (linearChainComplex (C := C) R V).d (m + 1) m ≫ sR m ≫ cR := by
      dsimp only [sR, cR]
      unfold SSet.ιChainComplex
      rw [subdivision_succ]
      erw [Sigma.ι_comp_desc]
      rfl
    have hsubS : SSet.ιChainComplex (X := linSSet V) (R := S) σ ≫ sS (m + 1) =
        SSet.ιChainComplex (X := linSSet V) (R := S) σ ≫
          (linearChainComplex (C := C) S V).d (m + 1) m ≫ sS m ≫ cS := by
      dsimp only [sS, cS]
      unfold SSet.ιChainComplex
      rw [subdivision_succ]
      erw [Sigma.ι_comp_desc]
      rfl
    have hdiff : (linearChainComplex (C := C) R V).d (m + 1) m ≫ Φ.f m =
        Φ.f (m + 1) ≫ (linearChainComplex (C := C) S V).d (m + 1) m := by
      exact (Φ.comm (m + 1) m).symm
    have hcone : cR ≫ Φ.f (m + 1) = Φ.f m ≫ cS := by
      dsimp only [cR, cS, Φ]
      exact coneMap_naturality_coefficient (C := C) a V (linSimplexBarycenter τ) m
    have hι : SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ Φ.f (m + 1) =
        a ≫ SSet.ιChainComplex (X := linSSet V) (R := S) σ := by
      exact _root_.SSet.ιChainComplex_coefficientMap_f (a := a) (X := linSSet V) (n := m + 1)
        (x := σ)
    calc SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ sR (m + 1) ≫ Φ.f (m + 1) =
          (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ sR (m + 1)) ≫ Φ.f (m + 1) := by
          exact (Category.assoc _ _ _).symm
        _ = (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              (linearChainComplex (C := C) R V).d (m + 1) m ≫ sR m ≫ cR) ≫ Φ.f (m + 1) := by
          exact congrArg (· ≫ Φ.f (m + 1)) hsub
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              (linearChainComplex (C := C) R V).d (m + 1) m ≫ sR m ≫ (Φ.f m ≫ cS) := by
          simp only [Category.assoc]
          rw [hcone]
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              (linearChainComplex (C := C) R V).d (m + 1) m ≫ (Φ.f m ≫ sS m) ≫ cS := by
          simp only [Category.assoc]
          erw [reassoc_of% ih]
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              (Φ.f (m + 1) ≫ (linearChainComplex (C := C) S V).d (m + 1) m) ≫
                sS m ≫ cS := by
          simp only [Category.assoc]
          erw [reassoc_of% hdiff]
        _ = (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ Φ.f (m + 1)) ≫
              (linearChainComplex (C := C) S V).d (m + 1) m ≫ sS m ≫ cS := by
          simp only [Category.assoc]
        _ = (a ≫ SSet.ιChainComplex (X := linSSet V) (R := S) σ) ≫
              (linearChainComplex (C := C) S V).d (m + 1) m ≫ sS m ≫ cS := by
          rw [hι]
        _ = a ≫ (SSet.ιChainComplex (X := linSSet V) (R := S) σ ≫
              (linearChainComplex (C := C) S V).d (m + 1) m ≫ sS m ≫ cS) := by
          simp only [Category.assoc]
        _ = a ≫ (SSet.ιChainComplex (X := linSSet V) (R := S) σ ≫ sS (m + 1)) := by
          rw [← hsubS]
        _ = (a ≫ SSet.ιChainComplex (X := linSSet V) (R := S) σ) ≫ sS (m + 1) := by
          simp only [Category.assoc]
        _ = (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ Φ.f (m + 1)) ≫ sS (m + 1) := by
          rw [← hι]
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              Φ.f (m + 1) ≫ sS (m + 1) := by
          simp only [Category.assoc]

@[reassoc]
theorem homotopyOp_naturality_coefficient
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) (V : Type w) [AddCommGroup V] [Module ℝ V] (n : ℕ) :
    homotopyOp (C := C) R V n ≫
        (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f (n + 1) =
      (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f n ≫
        homotopyOp (C := C) S V n := by
  let Φ : linearChainComplex (C := C) R V ⟶ linearChainComplex (C := C) S V :=
    (((SSet.chainComplexFunctor C).map a).app (linSSet V))
  let tR : ∀ k : ℕ, (linearChainComplex (C := C) R V).X k ⟶
      (linearChainComplex (C := C) R V).X (k + 1) :=
    fun k => homotopyOp (C := C) R V k
  let tS : ∀ k : ℕ, (linearChainComplex (C := C) S V).X k ⟶
      (linearChainComplex (C := C) S V).X (k + 1) :=
    fun k => homotopyOp (C := C) S V k
  change tR n ≫ Φ.f (n + 1) = Φ.f n ≫ tS n
  induction n with
  | zero =>
      apply SSet.chainComplex_hom_ext
      intro σ
      let τ : Fin 1 → V := σ
      let cR : (linearChainComplex (C := C) R V).X 0 ⟶
          (linearChainComplex (C := C) R V).X 1 :=
        coneMap (C := C) R V (linSimplexBarycenter τ) 0
      let cS : (linearChainComplex (C := C) S V).X 0 ⟶
          (linearChainComplex (C := C) S V).X 1 :=
        coneMap (C := C) S V (linSimplexBarycenter τ) 0
      have hzeroR : SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ tR 0 =
          SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ cR := by
        dsimp only [tR, cR]
        unfold SSet.ιChainComplex
        rw [homotopyOp_zero]
        erw [Sigma.ι_comp_desc]
        rfl
      have hzeroS : SSet.ιChainComplex (X := linSSet V) (R := S) σ ≫ tS 0 =
          SSet.ιChainComplex (X := linSSet V) (R := S) σ ≫ cS := by
        dsimp only [tS, cS]
        unfold SSet.ιChainComplex
        rw [homotopyOp_zero]
        erw [Sigma.ι_comp_desc]
        rfl
      have hcone : cR ≫ Φ.f 1 = Φ.f 0 ≫ cS := by
        dsimp only [cR, cS, Φ]
        exact coneMap_naturality_coefficient (C := C) a V (linSimplexBarycenter τ) 0
      have hι : SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ Φ.f 0 =
          a ≫ SSet.ιChainComplex (X := linSSet V) (R := S) σ := by
        exact _root_.SSet.ιChainComplex_coefficientMap_f (a := a) (X := linSSet V) (n := 0) (x := σ)
      calc
        SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ tR 0 ≫ Φ.f 1 =
            (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ tR 0) ≫ Φ.f 1 := by
          exact (Category.assoc _ _ _).symm
        _ = (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ cR) ≫ Φ.f 1 := by
          exact congrArg (· ≫ Φ.f 1) hzeroR
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ (Φ.f 0 ≫ cS) := by
          simp only [Category.assoc]; rw [hcone]
        _ = (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ Φ.f 0) ≫ cS := by
          simp only [Category.assoc]
        _ = (a ≫ SSet.ιChainComplex (X := linSSet V) (R := S) σ) ≫ cS := by
          rw [hι]
        _ = a ≫ (SSet.ιChainComplex (X := linSSet V) (R := S) σ ≫ cS) := by
          simp only [Category.assoc]
        _ = a ≫ (SSet.ιChainComplex (X := linSSet V) (R := S) σ ≫ tS 0) := by
          rw [← hzeroS]
        _ = (a ≫ SSet.ιChainComplex (X := linSSet V) (R := S) σ) ≫ tS 0 := by
          simp only [Category.assoc]
        _ = (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ Φ.f 0) ≫ tS 0 := by
          rw [← hι]
        _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ Φ.f 0 ≫ tS 0 := by
          simp only [Category.assoc]
  | succ m ih =>
      apply SSet.chainComplex_hom_ext
      intro σ
      let τ : Fin (m + 2) → V := σ
      let cR : (linearChainComplex (C := C) R V).X (m + 1) ⟶
          (linearChainComplex (C := C) R V).X (m + 2) :=
        coneMap (C := C) R V (linSimplexBarycenter τ) (m + 1)
      let cS : (linearChainComplex (C := C) S V).X (m + 1) ⟶
          (linearChainComplex (C := C) S V).X (m + 2) :=
        coneMap (C := C) S V (linSimplexBarycenter τ) (m + 1)
      let qR : (linearChainComplex (C := C) R V).X (m + 1) ⟶
          (linearChainComplex (C := C) R V).X (m + 1) :=
        𝟙 _ - (linearChainComplex (C := C) R V).d (m + 1) m ≫ tR m
      let qS : (linearChainComplex (C := C) S V).X (m + 1) ⟶
          (linearChainComplex (C := C) S V).X (m + 1) :=
        𝟙 _ - (linearChainComplex (C := C) S V).d (m + 1) m ≫ tS m
      have hsuccR : SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ tR (m + 1) =
          SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ qR ≫ cR := by
        dsimp only [tR, qR, cR]
        unfold SSet.ιChainComplex
        rw [homotopyOp_succ]
        erw [Sigma.ι_comp_desc]
        rfl
      have hsuccS : SSet.ιChainComplex (X := linSSet V) (R := S) σ ≫ tS (m + 1) =
          SSet.ιChainComplex (X := linSSet V) (R := S) σ ≫ qS ≫ cS := by
        dsimp only [tS, qS, cS]
        unfold SSet.ιChainComplex
        rw [homotopyOp_succ]
        erw [Sigma.ι_comp_desc]
        rfl
      have hdiff : (linearChainComplex (C := C) R V).d (m + 1) m ≫ Φ.f m =
          Φ.f (m + 1) ≫ (linearChainComplex (C := C) S V).d (m + 1) m := by
        exact (Φ.comm (m + 1) m).symm
      have hq : qR ≫ Φ.f (m + 1) = Φ.f (m + 1) ≫ qS := by
        dsimp only [qR, qS]
        simp only [Preadditive.sub_comp, Preadditive.comp_sub,
          Category.id_comp, Category.comp_id, Category.assoc]
        rw [ih]
        erw [reassoc_of% hdiff]
      have hcone : cR ≫ Φ.f (m + 2) = Φ.f (m + 1) ≫ cS := by
        dsimp only [cR, cS, Φ]
        exact coneMap_naturality_coefficient (C := C) a V (linSimplexBarycenter τ) (m + 1)
      have hι : SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ Φ.f (m + 1) =
          a ≫ SSet.ιChainComplex (X := linSSet V) (R := S) σ := by
        exact _root_.SSet.ιChainComplex_coefficientMap_f (a := a) (X := linSSet V) (n := m + 1)
          (x := σ)
      calc SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              tR (m + 1) ≫ Φ.f (m + 2) =
            (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
              tR (m + 1)) ≫ Φ.f (m + 2) := by
            exact (Category.assoc _ _ _).symm
          _ = (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ qR ≫ cR) ≫
                Φ.f (m + 2) := by
            exact congrArg (· ≫ Φ.f (m + 2)) hsuccR
          _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
                qR ≫ (Φ.f (m + 1) ≫ cS) := by
            simp only [Category.assoc]
            rw [hcone]
          _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
                (Φ.f (m + 1) ≫ qS) ≫ cS := by
            simp only [Category.assoc]
            erw [reassoc_of% hq]
          _ = (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ Φ.f (m + 1)) ≫ qS ≫ cS := by
            simp only [Category.assoc]
          _ = (a ≫ SSet.ιChainComplex (X := linSSet V) (R := S) σ) ≫ qS ≫ cS := by
            rw [hι]
          _ = a ≫ (SSet.ιChainComplex (X := linSSet V) (R := S) σ ≫ qS ≫ cS) := by
            simp only [Category.assoc]
          _ = a ≫ (SSet.ιChainComplex (X := linSSet V) (R := S) σ ≫ tS (m + 1)) := by
            rw [← hsuccS]
          _ = (a ≫ SSet.ιChainComplex (X := linSSet V) (R := S) σ) ≫ tS (m + 1) := by
            simp only [Category.assoc]
          _ = (SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫ Φ.f (m + 1)) ≫ tS (m + 1) := by
            rw [← hι]
          _ = SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
                Φ.f (m + 1) ≫ tS (m + 1) := by
            simp only [Category.assoc]

@[reassoc]
theorem linearSubdivisionHom_naturality_coefficient
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) (V : Type w) [AddCommGroup V] [Module ℝ V] :
    (((SSet.chainComplexFunctor C).map a).app (linSSet V)) ≫
        linearSubdivisionHom (C := C) S V =
      linearSubdivisionHom (C := C) R V ≫
        (((SSet.chainComplexFunctor C).map a).app (linSSet V)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  dsimp [linearSubdivisionHom]
  exact (subdivision_naturality_coefficient (C := C) (a := a) (V := V) n).symm

@[reassoc]
theorem linearSubdivisionHomotopy_naturality_coefficient
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) (V : Type w) [AddCommGroup V] [Module ℝ V] (i j : ℕ) :
    (linearSubdivisionHomotopy (C := C) R V).hom i j ≫
        (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f j =
      (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f i ≫
        (linearSubdivisionHomotopy (C := C) S V).hom i j := by
  by_cases h : i + 1 = j
  · subst h
    simp only [linearSubdivisionHomotopy_succ_component]
    exact homotopyOp_naturality_coefficient (C := C) a V _
  · simp only [linearSubdivisionHomotopy_eq_zero_of_ne _ _ h, Limits.zero_comp, Limits.comp_zero]

end AlgebraicTopology
