/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author : Avocado
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# Linear chains and cone contraction

Affine simplices in a type `Y` and the linear chain complex `LC_*(Y; R)`,
parameterized by a coefficient object `R : C` in an arbitrary preadditive category `C`
with the required coproducts. The simplicial object
`freemod R Y` has in degree `n` a coproduct of copies of `R` indexed by affine
`n`-simplices `Fin (n+1) → Y`. Its associated alternating face-map complex is
`linearChainComplex R Y`. The unaugmented complex of a nonempty affine set is
homotopy equivalent to `R` concentrated in degree zero; the augmented complex has
an extra degeneracy giving a contraction.

## Main definitions
* `linSSet`
* `linearChainComplex`
* `freemod`
* `coneMap`
* `linSSetAugmented`
* `coneExtraDegeneracy`
* `linearChainComplexHomotopyEquiv`
* `sigma_ι_comp_coneMap`
* `sigma_ι_comp_freemod_δ`

## Main results
* `coneMap_comp_δ_zero`
* `coneMap_boundary`
-/

@[expose] public section

open scoped BigOperators
open CategoryTheory Simplicial SimplexCategory SimplicialObject Matrix Limits Opposite

namespace AlgebraicTopology

universe u v w

/-- The simplicial set of affine simplices in `Y`: an `n`-simplex is a tuple `Fin (n+1) → Y`. -/
def linSSet (Y : Type w) : SSet.{w} where
  obj m := Fin (m.unop.len + 1) → Y
  map f := TypeCat.ofHom (fun g => g ∘ Hom.toOrderHom f.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

def linSSetFunctor : Type w ⥤ SSet.{w} where
  obj := linSSet
  map f :=
    { app := fun _ => TypeCat.ofHom (fun σ => f ∘ σ)
      naturality _ _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
lemma linSSetFunctor_map_app {V W : Type w} (f : V → W)
    (n : SimplexCategoryᵒᵖ) (σ : (linSSet V).obj n) :
    ConcreteCategory.hom ((linSSetFunctor.map (TypeCat.ofHom f)).app n) σ =
      f ∘ σ := rfl

/-- The simplicial object whose `n`-simplices are a coproduct of copies of `R` indexed by
affine `n`-simplices in `Y`. -/
noncomputable def freemod {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (Y : Type w) : SimplicialObject C :=
  linSSet (Y := Y) ⋙ sigmaConst.obj R

/-- The linear chain complex `LC_*(Y; R)` with coefficients in `R`. -/
noncomputable abbrev linearChainComplex {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (R : C) (Y : Type w) : ChainComplex C ℕ :=
  (linSSet Y).chainComplex R

noncomputable def linearChainComplexFunctor {C : Type u} [Category.{v} C]
    [Preadditive C] [HasCoproducts.{w} C] (R : C) : Type w ⥤ ChainComplex C ℕ :=
  linSSetFunctor ⋙ (SSet.chainComplexFunctor C).obj R

@[reassoc]
lemma linearChainComplexFunctor_map_ι
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) {V W : Type w} (f : V → W) {n : ℕ}
    (σ : (linSSet V).obj (Opposite.op ⦋n⦌)) :
    SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
        ((linearChainComplexFunctor R).map (TypeCat.ofHom f)).f n =
      SSet.ιChainComplex (X := linSSet W) (R := R) (f ∘ σ) := by
  change SSet.ιChainComplex (X := linSSet V) (R := R) σ ≫
      (SSet.chainComplexMap
        ((linSSetFunctor).map (TypeCat.ofHom f)) R).f n = _
  erw [SSet.ι_chainComplexMap_f]
  rfl

/-- The cone operator: prepend apex `b`. -/
noncomputable def coneMap {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (Y : Type w) (b : Y) (n : ℕ) :
    (freemod (C := C) R Y).obj (Opposite.op ⦋n⦌) ⟶
      (freemod (C := C) R Y).obj (Opposite.op ⦋n + 1⦌) :=
  (sigmaConst.obj R).map (TypeCat.ofHom (fun σ => vecCons b σ))

section ConeBoundary

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
variable {R : C} {V : Type w} {b : V}

lemma coneMap_comp_δ (n : ℕ) (i : Fin (n + 2)) :
    coneMap (C := C) R V b n ≫ (freemod (C := C) R V).δ i
      = (sigmaConst.obj (C := C) R).map
          (TypeCat.ofHom (fun σ : Fin (n + 1) → V => (vecCons b σ) ∘ Fin.succAbove i)) := by
  change (sigmaConst.obj (C := C) R).map (TypeCat.ofHom (fun σ : Fin (n + 1) → V => vecCons b σ))
      ≫ (freemod (C := C) R V).δ i = _
  rw [SimplicialObject.δ]
  change (sigmaConst.obj (C := C) R).map (TypeCat.ofHom (vecCons (α := V) b))
      ≫ (sigmaConst.obj (C := C) R).map
          (TypeCat.ofHom (fun σ : Fin (n + 2) → V => σ ∘ Fin.succAbove i)) = _
  rw [← (sigmaConst.obj (C := C) R).map_comp]
  rfl

lemma coneMap_comp_δ_zero (n : ℕ) :
    coneMap (C := C) (R := R) V b n ≫ (freemod (C := C) R V).δ 0 = 𝟙 _ := by
  rw [coneMap_comp_δ]
  have h : (fun σ : Fin (n + 1) → V => (vecCons b σ) ∘ Fin.succAbove 0) = id := by
    funext σ
    funext j
    simp only [Function.comp_apply, Fin.succAbove_zero, cons_val_succ, id_eq]
  rw [h]
  exact (sigmaConst.obj (C := C) R).map_id _

lemma coneMap_comp_δ_succ (n : ℕ) (k : Fin (n + 2)) :
    coneMap (C := C) (R := R) V b (n + 1) ≫ (freemod (C := C) R V).δ k.succ =
      (freemod (C := C) R V).δ k ≫ coneMap (C := C) R V b n := by
  have hrhs : (freemod (C := C) R V).δ k ≫ coneMap (C := C) R V b n
      = (sigmaConst.obj (C := C) R).map
          (TypeCat.ofHom (fun σ : Fin (n + 2) → V => vecCons b (σ ∘ Fin.succAbove k))) := by
    change (freemod (C := C) R V).δ k ≫
        (sigmaConst.obj (C := C) R).map (TypeCat.ofHom (fun σ : Fin (n + 1) → V => vecCons b σ)) = _
    rw [SimplicialObject.δ]
    change (sigmaConst.obj (C := C) R).map
          (TypeCat.ofHom (fun σ : Fin (n + 2) → V => σ ∘ Fin.succAbove k))
        ≫ (sigmaConst.obj (C := C) R).map (TypeCat.ofHom (vecCons (α := V) b)) = _
    rw [← (sigmaConst.obj (C := C) R).map_comp]
    rfl
  rw [coneMap_comp_δ, hrhs]
  have h_eq : (fun σ : Fin (n + 2) → V => (vecCons b σ) ∘ Fin.succAbove k.succ) =
      (fun σ : Fin (n + 2) → V => vecCons b (σ ∘ Fin.succAbove k)) := by
    funext σ
    funext j
    refine Fin.cases ?_ (fun l => ?_) j <;>
      simp only [Function.comp_apply, Fin.succ_succAbove_zero,
        Fin.succ_succAbove_succ, cons_val_zero, cons_val_succ]
  rw [h_eq]

lemma coneMap_boundary (n : ℕ) :
    coneMap (C := C) (R := R) V b (n + 1) ≫
        (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • (freemod (C := C) R V).δ i)
      + (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (freemod (C := C) R V).δ i) ≫
        coneMap (C := C) R V b n = 𝟙 _ := by
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, pow_zero, one_smul,
    coneMap_comp_δ_zero (C := C), coneMap_comp_δ_succ (C := C)]
  rw [add_assoc, ← Finset.sum_add_distrib, Finset.sum_eq_zero, add_zero]
  intro k _
  rw [pow_succ, mul_neg, mul_one, neg_smul, neg_add_cancel]

lemma coneMap_comp_sum (n : ℕ) :
    coneMap (C := C) (R := R) V b (n + 1) ≫
        (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • (freemod (C := C) R V).δ i)
      = 𝟙 _ - (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (freemod (C := C) R V).δ i) ≫
          coneMap (C := C) R V b n :=
  eq_sub_of_add_eq (coneMap_boundary (C := C) (n := n) (b := b))

@[reassoc]
lemma sigma_ι_comp_coneMap (b : V) {k : ℕ} (tau : Fin (k + 1) → V) :
    SSet.ιChainComplex (X := linSSet (Y := V)) (R := R) tau ≫ coneMap (C := C) R V b k =
      SSet.ιChainComplex (X := linSSet (Y := V)) (R := R) (Matrix.vecCons b tau) := by
  change Sigma.ι (fun _ : Fin (k + 1) → V ↦ (R : C)) tau ≫
      (sigmaConst.obj (C := C) R).map (TypeCat.ofHom (fun σ : Fin (k + 1) → V => vecCons b σ)) = _
  rw [sigmaConst_obj_map (C := C)]
  erw [Sigma.ι_comp_map']
  exact Category.id_comp _

@[reassoc]
lemma coneMap_naturality {W : Type w} (f : V → W) (b : V) (n : ℕ) :
    coneMap (C := C) R V b n ≫
        ((linearChainComplexFunctor R).map (TypeCat.ofHom f)).f (n + 1) =
      ((linearChainComplexFunctor R).map (TypeCat.ofHom f)).f n ≫
        coneMap (C := C) R W (f b) n := by
  change (sigmaConst.obj R).map
        (TypeCat.ofHom (fun σ : Fin (n + 1) → V => Matrix.vecCons b σ)) ≫
      (sigmaConst.obj R).map
        (TypeCat.ofHom (fun σ : Fin (n + 2) → V => f ∘ σ)) =
    (sigmaConst.obj R).map
        (TypeCat.ofHom (fun σ : Fin (n + 1) → V => f ∘ σ)) ≫
      (sigmaConst.obj R).map
        (TypeCat.ofHom (fun σ : Fin (n + 1) → W => Matrix.vecCons (f b) σ))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext σ i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

end ConeBoundary

/-- The affine simplices in `Y`, augmented by collapse to a point. -/
def linSSetAugmented (Y : Type w) : SimplicialObject.Augmented (Type w) :=
  SimplicialObject.augment (linSSet (Y := Y)) (PUnit : Type w)
    (TypeCat.ofHom (fun _ : Fin 1 → Y => PUnit.unit))
    (by intros; rfl)

section ConeContraction

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
variable {R : C} {Y : Type w} {b : Y}

private lemma cons_comp_succAbove_zero {n : ℕ} (g : Fin (n + 1) → Y) :
    vecCons b g ∘ Fin.succAbove 0 = g := by
  funext j
  simp only [Function.comp_apply, Fin.succAbove_zero, cons_val_succ]

private lemma cons_comp_succAbove_succ {n : ℕ} (i : Fin (n + 2)) (g : Fin (n + 2) → Y) :
    vecCons b g ∘ Fin.succAbove i.succ = vecCons b (g ∘ Fin.succAbove i) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;>
    simp only [Function.comp_apply, Fin.succ_succAbove_zero, Fin.succ_succAbove_succ,
      cons_val_zero, cons_val_succ]

private lemma cons_comp_predAbove_succ {n : ℕ} (i : Fin (n + 1)) (g : Fin (n + 1) → Y) :
    vecCons b g ∘ Fin.predAbove i.succ = vecCons b (g ∘ Fin.predAbove i) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp

/-- Prepending cone point `b` is an extra degeneracy. -/
noncomputable def coneExtraDegeneracy (Y : Type w) (b : Y) :
    (linSSetAugmented (Y := Y)).ExtraDegeneracy where
  s' := TypeCat.ofHom (fun _ : PUnit => fun _ : Fin 1 => b)
  s n := TypeCat.ofHom (fun g => vecCons b g)
  s'_comp_ε := rfl
  s₀_comp_δ₁ := by
    ext g
    change vecCons b g ∘ Fin.succAbove 1 = fun _ => b
    funext j
    fin_cases j
    rfl
  s_comp_δ₀ := by
    intro n
    ext g
    exact cons_comp_succAbove_zero (b := b) g
  s_comp_δ := by
    intro n i
    ext g
    exact cons_comp_succAbove_succ (b := b) i g
  s_comp_σ := by
    intro n i
    ext g
    exact cons_comp_predAbove_succ (b := b) i g

/-- Linear chain complex of a nonempty affine simplex set is homotopy equivalent to `R`
concentrated in degree zero. -/
noncomputable def linearChainComplexHomotopyEquiv {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] [Limits.HasZeroObject C] (R : C) (Y : Type w) (b : Y) :
    HomotopyEquiv (linearChainComplex (C := C) R Y)
      ((ChainComplex.single₀ C).obj
        ((sigmaConst.obj (C := C) R).obj (PUnit : Type w))) :=
  ((coneExtraDegeneracy (Y := Y) b).map (sigmaConst.obj (C := C) R)).homotopyEquiv

end ConeContraction

section SSetLemmas

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)

lemma sset_chainComplex_d (S : SSet.{w}) (n : ℕ) :
    (((SSet.chainComplexFunctor C).obj R).obj S).d (n + 1) n
      = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)
          • SimplicialObject.δ (S ⋙ sigmaConst.obj (C := C) R) i :=
  AlternatingFaceMapComplex.obj_d_eq (S ⋙ sigmaConst.obj (C := C) R) n

omit [Preadditive C] in
lemma sigmaConst_map_ι {α β : Type w} (g : α ⟶ β) (a : α) :
    Sigma.ι (fun _ : α => (R : C)) a
        ≫ (sigmaConst.obj (C := C) R).map g
      = Sigma.ι (fun _ : β => (R : C)) (g a) := by
  rw [sigmaConst_obj_map (C := C)]
  erw [Sigma.ι_comp_map']
  exact Category.id_comp _

@[reassoc]
lemma sigma_ι_comp_freemod_δ {V : Type w} {k : ℕ} (tau : Fin (k + 2) → V) (i : Fin (k + 2)) :
    Sigma.ι (fun _ : Fin (k + 2) → V ↦ (R : C)) tau ≫ (freemod (C := C) R V).δ i =
      Sigma.ι (fun _ : Fin (k + 1) → V ↦ (R : C)) (tau ∘ Fin.succAbove i) := by
  rw [SimplicialObject.δ]
  change Sigma.ι (fun _ : Fin (k + 2) → V ↦ (R : C)) tau ≫
      (sigmaConst.obj (C := C) R).map
        (TypeCat.ofHom (fun σ : Fin (k + 2) → V => σ ∘ Fin.succAbove i)) = _
  rw [sigmaConst_map_ι (C := C) (R := R)]
  rfl

omit [Preadditive C] in
lemma sigma_ι_comp_sset_δ (S : SSet.{w}) {n : ℕ} (x : S.obj (Opposite.op ⦋n + 1⦌))
    (i : Fin (n + 2)) :
    Sigma.ι (fun _ : S.obj (Opposite.op ⦋n + 1⦌) => (R : C)) x
        ≫ SimplicialObject.δ (S ⋙ sigmaConst.obj (C := C) R) i
      = Sigma.ι (fun _ : S.obj (Opposite.op ⦋n⦌) => (R : C)) (S.δ i x) := by
  change Sigma.ι _ x ≫ (sigmaConst.obj (C := C) R).map ((S).map (SimplexCategory.δ i).op) = _
  rw [sigmaConst_map_ι (C := C) (R := R)]
  rfl

lemma sigma_ι_comp_sset_d (S : SSet.{w}) {n : ℕ} (x : S.obj (Opposite.op ⦋n + 1⦌)) :
    Sigma.ι (fun _ : S.obj (Opposite.op ⦋n + 1⦌) => (R : C)) x
        ≫ (((SSet.chainComplexFunctor C).obj R).obj S).d (n + 1) n
      = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ)
          • Sigma.ι (fun _ : S.obj (Opposite.op ⦋n⦌) => (R : C)) (S.δ i x) := by
  rw [sset_chainComplex_d (C := C) (R := R)]
  erw [Preadditive.comp_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  erw [Preadditive.comp_zsmul]
  exact congrArg ((-1 : ℤ) ^ (i : ℕ) • ·)
    (sigma_ι_comp_sset_δ (C := C) (R := R) S x i)
end SSetLemmas

@[reassoc]
lemma _root_.SSet.ιChainComplex_coefficientMap_f
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) (X : SSet.{w}) (n : ℕ)
    (x : X.obj (Opposite.op (SimplexCategory.mk n))) :
    X.ιChainComplex (R := R) x ≫
        (((SSet.chainComplexFunctor C).map a).app X).f n =
      a ≫ X.ιChainComplex (R := S) x := by
  change Sigma.ι (fun _ : X.obj (Opposite.op (SimplexCategory.mk n)) => (R : C)) x ≫
      Limits.Sigma.map (fun _ : X.obj (Opposite.op (SimplexCategory.mk n)) => a) =
    a ≫ Sigma.ι (fun _ : X.obj (Opposite.op (SimplexCategory.mk n)) => (S : C)) x
  rw [Limits.Sigma.ι_map]

@[reassoc]
lemma coneMap_naturality_coefficient
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {R S : C} (a : R ⟶ S) (V : Type w) (b : V) (n : ℕ) :
    coneMap (C := C) R V b n ≫
        (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f (n + 1) =
      (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f n ≫
        coneMap (C := C) S V b n := by
  let φ_n : ((linSSet V).chainComplex R).X n ⟶ ((linSSet V).chainComplex S).X n :=
    (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f n
  let φ_succ : ((linSSet V).chainComplex R).X (n + 1) ⟶ ((linSSet V).chainComplex S).X (n + 1) :=
    (((SSet.chainComplexFunctor C).map a).app (linSSet V)).f (n + 1)
  let cR : ((linSSet V).chainComplex R).X n ⟶ ((linSSet V).chainComplex R).X (n + 1) :=
    coneMap (C := C) R V b n
  let cS : ((linSSet V).chainComplex S).X n ⟶ ((linSSet V).chainComplex S).X (n + 1) :=
    coneMap (C := C) S V b n
  change cR ≫ φ_succ = φ_n ≫ cS
  apply SSet.chainComplex_hom_ext
  intro x
  have h1 : SSet.ιChainComplex (X := linSSet V) (R := R) x ≫ cR =
      SSet.ιChainComplex (X := linSSet V) (R := R) (Matrix.vecCons b x) :=
    sigma_ι_comp_coneMap (C := C) (R := R) b x
  have h2 : SSet.ιChainComplex (X := linSSet V) (R := R) (Matrix.vecCons b x) ≫ φ_succ =
      a ≫ SSet.ιChainComplex (X := linSSet V) (R := S) (Matrix.vecCons b x) :=
    _root_.SSet.ιChainComplex_coefficientMap_f (a := a) (X := linSSet V) (n := n + 1)
      (x := Matrix.vecCons b x)
  have h3 : SSet.ιChainComplex (X := linSSet V) (R := S) (Matrix.vecCons b x) =
      SSet.ιChainComplex (X := linSSet V) (R := S) x ≫ cS :=
    (sigma_ι_comp_coneMap (C := C) (R := S) b x).symm
  have h_left : SSet.ιChainComplex (X := linSSet V) (R := R) x ≫ (cR ≫ φ_succ) =
        a ≫ SSet.ιChainComplex (X := linSSet V) (R := S) (Matrix.vecCons b x) := by
    rw [← Category.assoc, h1, h2]
  have h_right : SSet.ιChainComplex (X := linSSet V) (R := R) x ≫ (φ_n ≫ cS) =
        a ≫ SSet.ιChainComplex (X := linSSet V) (R := S) (Matrix.vecCons b x) := by
    rw [← Category.assoc,
      _root_.SSet.ιChainComplex_coefficientMap_f (a := a) (X := linSSet V) (n := n)
        (x := x), Category.assoc, ← h3]
  rw [h_left, h_right]

end AlgebraicTopology
