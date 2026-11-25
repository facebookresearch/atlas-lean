/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.ExactLimits
public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialFunctorComparison
public import MathlibExt.Algebra.Homology.ExactSequenceFour
public import MathlibExt.Algebra.Category.Grp.SequentialMittagLeffler
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

public import MathlibExt.Algebra.Homology.HomologyMapSquare

/-!
# Milnor short exact sequences for inverse towers of complexes

This file constructs the canonical Milnor short exact sequence associated to
an inverse tower of homological complexes.  Its input is the exactness of the
standard product difference on the tower of complexes.  Its endpoints are the
concrete sequential `lim¹` of the next homology tower and the inverse limit
of the current homology tower.

The construction uses the short exact product-difference sequence of
complexes, Mathlib's long homology sequence, and the canonical comparison
between homology of an exact countable product and the product of homologies.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace HomologicalComplex

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι}
  [HasCountableProducts C] [_exactProducts : CountableAB4Star C]
  [HasLimitsOfShape ℕᵒᵖ C]

omit [CountableAB4Star C] [HasLimitsOfShape ℕᵒᵖ C] in
/-- Countable products of homological complexes are computed degreewise. -/
noncomputable instance homologicalComplexHasCountableProducts :
    HasCountableProducts (HomologicalComplex C c) where
  out _ := inferInstance

/-- The inverse tower of degree-`i` homology objects of a tower of complexes. -/
abbrev sequentialHomologyTower
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) : ℕᵒᵖ ⥤ C where
  obj n := (K.obj n).homology i
  map f := (K ⋙ homologyFunctor C c i).map f
  map_id n := (K ⋙ homologyFunctor C c i).map_id n
  map_comp f g := (K ⋙ homologyFunctor C c i).map_comp f g

omit [HasCountableProducts C] [CountableAB4Star C] [HasLimitsOfShape ℕᵒᵖ C] in
/-- The explicit object presentation retains the entire native composite.
It lets projection formulas use actual homology objects without unfolding the native functor. -/
theorem sequentialHomologyTower_eq_comp
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) :
    sequentialHomologyTower K i = K ⋙ homologyFunctor C c i := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Exact countable products canonically identify the homology of the
sequential product complex with the sequential product of homology objects. -/
noncomputable def sequentialProductHomologyIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) :
    (sequentialProduct K).homology i ≅
      sequentialProduct (sequentialHomologyTower K i) :=
  PreservesProduct.iso (homologyFunctor C c i)
    (fun n : ℕ => K.obj (op n))

set_option backward.isDefEq.respectTransparency false in
omit [HasLimitsOfShape ℕᵒᵖ C] in
/-- Every product coordinate of the product-homology comparison is the
homology map of the corresponding product projection. -/
@[reassoc (attr := simp)]
theorem sequentialProductHomologyIso_hom_π
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) (n : ℕ) :
    (sequentialProductHomologyIso K i).hom ≫
        Pi.π (fun n : ℕ => (K.obj (op n)).homology i) n =
      homologyMap (Pi.π (fun n : ℕ => K.obj (op n)) n) i := by
  change
    (PreservesProduct.iso (homologyFunctor C c i)
        (fun n : ℕ => K.obj (op n))).hom ≫
        Pi.π (fun n : ℕ =>
          (homologyFunctor C c i).obj (K.obj (op n))) n =
      (homologyFunctor C c i).map
        (Pi.π (fun n : ℕ => K.obj (op n)) n)
  rw [PreservesProduct.iso_hom, piComparison_comp_π]

set_option backward.isDefEq.respectTransparency false in
omit [HasLimitsOfShape ℕᵒᵖ C] in
/-- Under the exact-product comparison, the homology map of the complex-level
standard difference is the standard difference of the homology tower. -/
theorem homologyMap_sequentialDifference_comp_productHomologyIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) :
    homologyMap (sequentialDifference K) i ≫
        (sequentialProductHomologyIso K i).hom =
      (sequentialProductHomologyIso K i).hom ≫
        sequentialDifference (sequentialHomologyTower K i) := by
  change (homologyFunctor C c i).map (sequentialDifference K) ≫
      (PreservesProduct.iso (homologyFunctor C c i) (fun n : ℕ => K.obj (op n))).hom =
    (PreservesProduct.iso (homologyFunctor C c i) (fun n : ℕ => K.obj (op n))).hom ≫
      sequentialDifference (K ⋙ homologyFunctor C c i)
  simp only [PreservesProduct.iso_hom]
  exact sequentialDifference_piComparison (homologyFunctor C c i) K

/-- The inverse tower obtained by evaluating a tower of complexes in one
degree. -/
abbrev sequentialDegreeTower
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) : ℕᵒᵖ ⥤ C :=
  K ⋙ eval C c i

omit [CountableAB4Star C] [HasLimitsOfShape ℕᵒᵖ C] in
/-- Evaluation in one degree canonically commutes with the sequential
product of complexes. -/
noncomputable def sequentialProductEvalIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) :
    (sequentialProduct K).X i ≅
      sequentialProduct (sequentialDegreeTower K i) :=
  PreservesProduct.iso (eval C c i) (fun n : ℕ => K.obj (op n))

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] [HasLimitsOfShape ℕᵒᵖ C] in
/-- Every coordinate of the degree-evaluation product comparison is the
evaluated product projection. -/
@[reassoc (attr := simp)]
theorem sequentialProductEvalIso_hom_π
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) (n : ℕ) :
    (sequentialProductEvalIso K i).hom ≫
        Pi.π (fun n : ℕ => (K.obj (op n)).X i) n =
      (Pi.π (fun n : ℕ => K.obj (op n)) n).f i := by
  change
    (PreservesProduct.iso (eval C c i)
        (fun n : ℕ => K.obj (op n))).hom ≫
        Pi.π (fun n : ℕ => (eval C c i).obj (K.obj (op n))) n =
      (eval C c i).map (Pi.π (fun n : ℕ => K.obj (op n)) n)
  rw [PreservesProduct.iso_hom, piComparison_comp_π]

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] [HasLimitsOfShape ℕᵒᵖ C] in
/-- Evaluation in one degree identifies the actual complex-level standard
difference with the standard difference of the evaluated tower. -/
theorem sequentialDifference_f_comp_productEvalIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) :
    (sequentialDifference K).f i ≫
        (sequentialProductEvalIso K i).hom =
      (sequentialProductEvalIso K i).hom ≫
        sequentialDifference (sequentialDegreeTower K i) := by
  change (eval C c i).map (sequentialDifference K) ≫
      (PreservesProduct.iso (eval C c i) (fun n : ℕ => K.obj (op n))).hom =
    (PreservesProduct.iso (eval C c i) (fun n : ℕ => K.obj (op n))).hom ≫
      sequentialDifference (K ⋙ eval C c i)
  simp only [PreservesProduct.iso_hom]
  exact sequentialDifference_piComparison (eval C c i) K

omit [CountableAB4Star C] [HasLimitsOfShape ℕᵒᵖ C] in
/-- Degreewise epimorphy of the standard differences implies epimorphy of
the actual standard difference of complexes. -/
theorem epi_sequentialDifference_of_epi_degreewise
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (h : ∀ i : ι, Epi
      (sequentialDifference (sequentialDegreeTower K i))) :
    Epi (sequentialDifference K) := by
  apply epi_of_epi_f
  intro i
  exact (epi_map_sequentialDifference_iff (eval C c i) K).2 (h i)

/-- A degreewise Mittag--Leffler tower of complexes of abelian groups has an
epimorphic actual product difference. -/
theorem _root_.AddCommGrpCat.epi_sequentialDifference_of_degreewise_isMittagLeffler
    (K : ℕᵒᵖ ⥤ HomologicalComplex AddCommGrpCat.{u} c)
    (h : ∀ i : ι,
      (sequentialDegreeTower K i).IsSequentialMittagLeffler) :
    Epi (sequentialDifference K) :=
  epi_sequentialDifference_of_epi_degreewise K fun i =>
    AddCommGrpCat.epi_sequentialDifference_of_isMittagLeffler _ (h i)

/-- The map of homology towers induced by a map of towers of complexes. -/
abbrev sequentialHomologyTowerMap
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c} (α : K ⟶ L) (i : ι) :
    sequentialHomologyTower K i ⟶ sequentialHomologyTower L i :=
  Functor.whiskerRight α (homologyFunctor C c i)

omit [HasCountableProducts C] [CountableAB4Star C]
  [HasLimitsOfShape ℕᵒᵖ C] in
/-- The homology-tower map induced by the identity is the identity. -/
theorem sequentialHomologyTowerMap_id
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) :
    sequentialHomologyTowerMap (𝟙 K) i =
      𝟙 (sequentialHomologyTower K i) := by
  exact Functor.whiskerRight_id' (homologyFunctor C c i)

omit [HasCountableProducts C] [CountableAB4Star C]
  [HasLimitsOfShape ℕᵒᵖ C] in
/-- Homology-tower maps preserve composition. -/
@[reassoc]
theorem sequentialHomologyTowerMap_comp
    {K L M : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (α : K ⟶ L) (β : L ⟶ M) (i : ι) :
    sequentialHomologyTowerMap (α ≫ β) i =
      sequentialHomologyTowerMap α i ≫
        sequentialHomologyTowerMap β i := by
  exact Functor.whiskerRight_comp α β (homologyFunctor C c i)

omit [HasLimitsOfShape ℕᵒᵖ C] in
/-- The exact-product homology comparison is natural in maps of towers. -/
@[reassoc]
theorem sequentialProductHomologyIso_naturality
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c} (α : K ⟶ L) (i : ι) :
    homologyMap (sequentialProductMap α) i ≫
        (sequentialProductHomologyIso L i).hom =
      (sequentialProductHomologyIso K i).hom ≫
        sequentialProductMap (sequentialHomologyTowerMap α i) := by
  change (homologyFunctor C c i).map (sequentialProductMap α) ≫
      (PreservesProduct.iso (homologyFunctor C c i) (fun n : ℕ => L.obj (op n))).hom =
    (PreservesProduct.iso (homologyFunctor C c i) (fun n : ℕ => K.obj (op n))).hom ≫
      sequentialProductMap (Functor.whiskerRight α (homologyFunctor C c i))
  simp only [PreservesProduct.iso_hom]
  exact sequentialProductMap_piComparison (homologyFunctor C c i) α

omit [HasLimitsOfShape ℕᵒᵖ C] in
/-- Inverse form of naturality for the exact-product homology comparison. -/
@[reassoc]
theorem sequentialProductHomologyIso_inv_naturality
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c} (α : K ⟶ L) (i : ι) :
    sequentialProductMap (sequentialHomologyTowerMap α i) ≫
        (sequentialProductHomologyIso L i).inv =
      (sequentialProductHomologyIso K i).inv ≫
        homologyMap (sequentialProductMap α) i := by
  apply (cancel_epi (sequentialProductHomologyIso K i).hom).1
  calc
    (sequentialProductHomologyIso K i).hom ≫
          (sequentialProductMap (sequentialHomologyTowerMap α i) ≫
            (sequentialProductHomologyIso L i).inv) =
        ((sequentialProductHomologyIso K i).hom ≫
          sequentialProductMap (sequentialHomologyTowerMap α i)) ≫
            (sequentialProductHomologyIso L i).inv :=
      (Category.assoc _ _ _).symm
    _ = (homologyMap (sequentialProductMap α) i ≫
          (sequentialProductHomologyIso L i).hom) ≫
            (sequentialProductHomologyIso L i).inv := by
      rw [sequentialProductHomologyIso_naturality]
    _ = homologyMap (sequentialProductMap α) i := by simp
    _ = ((sequentialProductHomologyIso K i).hom ≫
          (sequentialProductHomologyIso K i).inv) ≫
            homologyMap (sequentialProductMap α) i := by simp
    _ = (sequentialProductHomologyIso K i).hom ≫
          ((sequentialProductHomologyIso K i).inv ≫
            homologyMap (sequentialProductMap α) i) :=
      Category.assoc _ _ _

omit [CountableAB4Star C] in
/-- A map of towers induces the canonical map between their
limit-product-difference short complexes. -/
noncomputable def sequentialLimitShortComplexMap
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c} (α : K ⟶ L) :
    sequentialLimitShortComplex K ⟶ sequentialLimitShortComplex L where
  τ₁ := limMap α
  τ₂ := sequentialProductMap α
  τ₃ := sequentialProductMap α
  comm₁₂ := (sequentialLimitToProduct_naturality α).symm
  comm₂₃ := sequentialDifference_naturality α

omit [CountableAB4Star C] in
/-- The standard limit-product-difference complex is short exact whenever
the actual complex-level standard difference is an epimorphism. -/
theorem sequentialLimitShortComplex_shortExact_of_epi
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K)) :
    (sequentialLimitShortComplex K).ShortExact := by
  exact ShortComplex.ShortExact.mk'
    (sequentialLimitShortComplex_exact K) inferInstance hK

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] in
/-- The actual connecting map in the long homology sequence of the
limit-product-difference short exact complex. -/
noncomputable def sequentialLimitHomologyBoundary
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialProduct K).homology i ⟶ (limit K).homology j :=
  (sequentialLimitShortComplex_shortExact_of_epi K hK).δ i j hij

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] in
/-- The homology map of the canonical morphism from the inverse-limit
complex to the sequential product complex. -/
noncomputable def sequentialLimitHomologyToProduct
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (j : ι) :
    (limit K).homology j ⟶ (sequentialProduct K).homology j :=
  homologyMap (sequentialLimitToProduct K) j

omit [CountableAB4Star C] in
@[simp]
theorem sequentialLimitHomologyToProduct_eq
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (j : ι) :
    sequentialLimitHomologyToProduct K j =
      homologyMap (sequentialLimitToProduct K) j :=
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] in
/-- The homology map from the limit complex to the product complex is killed
by the homology map of the standard difference. -/
@[reassoc (attr := simp)]
theorem sequentialLimitHomologyToProduct_comp_difference
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (j : ι) :
    homologyMap (sequentialLimitToProduct K) j ≫
        homologyMap (sequentialDifference K) j = 0 := by
  rw [← homologyMap_comp,
    sequentialLimitToProduct_comp_difference, homologyMap_zero]

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] in
/-- The long-sequence boundary followed by the homology map to the product is
zero. -/
@[reassoc (attr := simp)]
theorem sequentialLimitHomologyBoundary_comp_toProduct
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialLimitHomologyBoundary K hK i j hij ≫
        homologyMap (sequentialLimitToProduct K) j = 0 :=
  (sequentialLimitShortComplex_shortExact_of_epi K hK).δ_comp i j hij

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] in
/-- The homology map of the product difference followed by the long-sequence
boundary is zero. -/
@[reassoc (attr := simp)]
theorem homologyMap_sequentialDifference_comp_boundary
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    homologyMap (sequentialDifference K) i ≫
        sequentialLimitHomologyBoundary K hK i j hij = 0 :=
  (sequentialLimitShortComplex_shortExact_of_epi K hK).comp_δ i j hij

omit [CountableAB4Star C] in
/-- Naturality of the actual long-homology-sequence boundary for the
limit-product-difference short exact complexes. -/
@[reassoc]
theorem sequentialLimitBoundary_naturality
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (hK : Epi (sequentialDifference K))
    (hL : Epi (sequentialDifference L))
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    sequentialLimitHomologyBoundary K hK i j hij ≫
        homologyMap (limMap α) j =
      homologyMap (sequentialProductMap α) i ≫
        sequentialLimitHomologyBoundary L hL i j hij :=
  HomologySequence.δ_naturality
    (sequentialLimitShortComplexMap α)
    (sequentialLimitShortComplex_shortExact_of_epi K hK)
    (sequentialLimitShortComplex_shortExact_of_epi L hL)
    i j hij

omit [CountableAB4Star C] in
/-- The five consecutive terms of the homology long exact sequence used in
the sequential Milnor construction. -/
noncomputable def sequentialMilnorHomologyWindow
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) : ComposableArrows C 4 := by
  let S := sequentialLimitShortComplex K
  let hS := sequentialLimitShortComplex_shortExact_of_epi K hK
  exact ComposableArrows.mk₄
    (homologyMap S.g i)
    (hS.δ i j hij)
    (homologyMap S.f j)
    (homologyMap S.g j)

omit [CountableAB4Star C] in
/-- The Milnor five-term homology window is exact. -/
theorem sequentialMilnorHomologyWindow_exact
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorHomologyWindow K hK i j hij).Exact := by
  let hS := sequentialLimitShortComplex_shortExact_of_epi K hK
  exact ComposableArrows.exact_of_δ₀
    (hS.homology_exact₃ i j hij).exact_toComposableArrows
    (ComposableArrows.exact_of_δ₀
      (hS.homology_exact₁ i j hij).exact_toComposableArrows
      (hS.homology_exact₂ j).exact_toComposableArrows)

omit [CountableAB4Star C] in
/-- The canonical cokernel-middle-kernel short complex extracted from the
five-term homology window. -/
noncomputable def sequentialMilnorRawShortComplex
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) : ShortComplex C :=
  ComposableArrows.exactSequenceFourShortComplex
    (sequentialMilnorHomologyWindow K hK i j hij)
    (sequentialMilnorHomologyWindow_exact K hK i j hij)

omit [CountableAB4Star C] in
/-- The extracted raw Milnor short complex is short exact. -/
theorem sequentialMilnorRawShortComplex_shortExact
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorRawShortComplex K hK i j hij).ShortExact :=
  ComposableArrows.exactSequenceFourShortComplex_shortExact
    (sequentialMilnorHomologyWindow K hK i j hij)
    (sequentialMilnorHomologyWindow_exact K hK i j hij)

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] in
/-- The quotient map into the raw short complex is the actual connecting map
in Mathlib's long homology sequence. -/
@[reassoc]
theorem sequentialMilnorRawShortComplex_π_f
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    cokernel.π (homologyMap (sequentialDifference K) i) ≫
        (sequentialMilnorRawShortComplex K hK i j hij).f =
      sequentialLimitHomologyBoundary K hK i j hij := by
  exact ComposableArrows.exactSequenceFourShortComplex_π_f
    (sequentialMilnorHomologyWindow K hK i j hij)
    (sequentialMilnorHomologyWindow_exact K hK i j hij)

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] in
/-- The raw right map followed by its kernel inclusion is the actual homology
map of the canonical limit-to-product morphism. -/
@[reassoc]
theorem sequentialMilnorRawShortComplex_g_ι
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorRawShortComplex K hK i j hij).g ≫
        kernel.ι (homologyMap (sequentialDifference K) j) =
      sequentialLimitHomologyToProduct K j := by
  exact ComposableArrows.exactSequenceFourShortComplex_g_ι
    (sequentialMilnorHomologyWindow K hK i j hij)
    (sequentialMilnorHomologyWindow_exact K hK i j hij)

set_option backward.isDefEq.respectTransparency false in
/-- The actual homology-product cokernel quotient, with codomain the left
object of the raw Milnor short complex. -/
noncomputable def sequentialMilnorRawCokernelπ
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialProduct K).homology i ⟶
      (sequentialMilnorRawShortComplex K hK i j hij).X₁ :=
  cokernel.π (homologyMap (sequentialDifference K) i)

set_option backward.isDefEq.respectTransparency false in
/-- The actual kernel inclusion, with domain the right object of the raw
Milnor short complex. -/
noncomputable def sequentialMilnorRawKernelι
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorRawShortComplex K hK i j hij).X₃ ⟶
      (sequentialProduct K).homology j :=
  kernel.ι (homologyMap (sequentialDifference K) j)

omit [CountableAB4Star C] in
/-- The raw cokernel quotient followed by the raw injection is the actual
long-sequence boundary. -/
@[reassoc]
theorem sequentialMilnorRawCokernelπ_f
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialMilnorRawCokernelπ K hK i j hij ≫
        (sequentialMilnorRawShortComplex K hK i j hij).f =
      sequentialLimitHomologyBoundary K hK i j hij :=
  sequentialMilnorRawShortComplex_π_f K hK i j hij

omit [CountableAB4Star C] in
/-- The raw edge followed by the raw kernel inclusion is the actual homology
map from the inverse-limit complex to the product complex. -/
@[reassoc]
theorem sequentialMilnorRawShortComplex_g_rawKernelι
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorRawShortComplex K hK i j hij).g ≫
        sequentialMilnorRawKernelι K hK i j hij =
      sequentialLimitHomologyToProduct K j :=
  sequentialMilnorRawShortComplex_g_ι K hK i j hij

/-- The cokernel of the homology map of the complex-level difference is
concrete sequential `lim¹` of the homology tower. -/
noncomputable def sequentialMilnorCokernelIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) :
    cokernel (homologyMap (sequentialDifference K) i) ≅
      sequentialLimOne (sequentialHomologyTower K i) :=
  sequentialDifferenceCokernelIso (homologyFunctor C c i) K

/-- The kernel of the homology map of the complex-level difference is the
chosen inverse limit of the homology tower. -/
noncomputable def sequentialMilnorKernelIsoLimit
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (j : ι) :
    kernel (homologyMap (sequentialDifference K) j) ≅
      limit (sequentialHomologyTower K j) :=
  sequentialDifferenceKernelIso (homologyFunctor C c j) K ≪≫
    (sequentialLimitKernelIso (sequentialHomologyTower K j)).symm

omit [HasLimitsOfShape ℕᵒᵖ C] in
/-- Inverse quotient formula for the direct cokernel-to-`lim¹`
identification. -/
@[reassoc]
theorem sequentialMilnorCokernelIso_inv_π
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) :
    sequentialLimOneπ (sequentialHomologyTower K i) ≫
        (sequentialMilnorCokernelIso K i).inv =
      (sequentialProductHomologyIso K i).inv ≫
        cokernel.π (homologyMap (sequentialDifference K) i) := by
  change
    cokernel.π (sequentialDifference (sequentialHomologyTower K i)) ≫
      (cokernel.mapIso
        (homologyMap (sequentialDifference K) i)
        (sequentialDifference (sequentialHomologyTower K i))
        (sequentialProductHomologyIso K i)
        (sequentialProductHomologyIso K i)
        (homologyMap_sequentialDifference_comp_productHomologyIso K i)).inv = _
  dsimp only [cokernel.mapIso, cokernel.map]
  rw [cokernel.π_desc]

/-- The direct kernel-to-limit identification followed by the product map is
the kernel inclusion followed by the exact-product homology comparison. -/
@[reassoc]
theorem sequentialMilnorKernelIsoLimit_hom_toProduct
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (j : ι) :
    (sequentialMilnorKernelIsoLimit K j).hom ≫
        sequentialLimitToProduct (sequentialHomologyTower K j) =
      kernel.ι (homologyMap (sequentialDifference K) j) ≫
        (sequentialProductHomologyIso K j).hom := by
  change
    ((kernel.mapIso
        (homologyMap (sequentialDifference K) j)
        (sequentialDifference (sequentialHomologyTower K j))
        (sequentialProductHomologyIso K j)
        (sequentialProductHomologyIso K j)
        (homologyMap_sequentialDifference_comp_productHomologyIso K j)).hom ≫
      (sequentialLimitKernelIso
        (sequentialHomologyTower K j)).inv) ≫
      sequentialLimitToProduct (sequentialHomologyTower K j) = _
  rw [Category.assoc,
    sequentialLimitKernelIso_inv_comp_toProduct]
  dsimp only [kernel.mapIso, kernel.map]
  rw [kernel.lift_ι]

/-- The left endpoint of the raw homology window is concrete sequential
`lim¹` of the degree-`i` homology tower. -/
noncomputable def sequentialMilnorLeftIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorRawShortComplex K hK i j hij).X₁ ≅
      sequentialLimOne (sequentialHomologyTower K i) := by
  change cokernel (homologyMap (sequentialDifference K) i) ≅ _
  exact sequentialMilnorCokernelIso K i

/-- The right endpoint of the raw homology window is the chosen inverse
limit of the degree-`j` homology tower. -/
noncomputable def sequentialMilnorRightIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorRawShortComplex K hK i j hij).X₃ ≅
      limit (sequentialHomologyTower K j) := by
  change kernel (homologyMap (sequentialDifference K) j) ≅ _
  exact sequentialMilnorKernelIsoLimit K j

/-- The left endpoint transport sends the homology-product cokernel quotient
to the product-homology comparison followed by the concrete `lim¹` quotient. -/
@[reassoc]
theorem sequentialMilnorLeftIso_π_hom
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    cokernel.π (homologyMap (sequentialDifference K) i) ≫
        (sequentialMilnorLeftIso K hK i j hij).hom =
      (sequentialProductHomologyIso K i).hom ≫
        sequentialLimOneπ (sequentialHomologyTower K i) := by
  change
    cokernel.π (homologyMap (sequentialDifference K) i) ≫
      (cokernel.mapIso
        (homologyMap (sequentialDifference K) i)
        (sequentialDifference (sequentialHomologyTower K i))
        (sequentialProductHomologyIso K i)
        (sequentialProductHomologyIso K i)
        (homologyMap_sequentialDifference_comp_productHomologyIso K i)).hom = _
  dsimp only [cokernel.mapIso, cokernel.map]
  rw [cokernel.π_desc]
  rfl

/-- Inverse quotient formula for the left raw endpoint transport. -/
@[reassoc]
private theorem sequentialMilnorLeftIso_inv_π_early
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialLimOneπ (sequentialHomologyTower K i) ≫
        (sequentialMilnorLeftIso K hK i j hij).inv =
      (sequentialProductHomologyIso K i).inv ≫
        cokernel.π (homologyMap (sequentialDifference K) i) := by
  change
    cokernel.π (sequentialDifference (sequentialHomologyTower K i)) ≫
      (cokernel.mapIso
        (homologyMap (sequentialDifference K) i)
        (sequentialDifference (sequentialHomologyTower K i))
        (sequentialProductHomologyIso K i)
        (sequentialProductHomologyIso K i)
        (homologyMap_sequentialDifference_comp_productHomologyIso K i)).inv = _
  dsimp only [cokernel.mapIso, cokernel.map]
  rw [cokernel.π_desc]

set_option backward.isDefEq.respectTransparency false in
/-- Type-stable inverse quotient formula using the raw left endpoint. -/
@[reassoc]
private theorem sequentialMilnorLeftIso_inv_rawCokernelπ_early
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialLimOneπ (sequentialHomologyTower K i) ≫
        (sequentialMilnorLeftIso K hK i j hij).inv =
      (sequentialProductHomologyIso K i).inv ≫
        sequentialMilnorRawCokernelπ K hK i j hij :=
  sequentialMilnorLeftIso_inv_π_early K hK i j hij

/-- The right endpoint transport followed by the product inclusion is the
raw kernel inclusion followed by the product-homology comparison. -/
@[reassoc]
theorem sequentialMilnorRightIso_hom_toProduct
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorRightIso K hK i j hij).hom ≫
        sequentialLimitToProduct (sequentialHomologyTower K j) =
      kernel.ι (homologyMap (sequentialDifference K) j) ≫
        (sequentialProductHomologyIso K j).hom := by
  change
    ((kernel.mapIso
        (homologyMap (sequentialDifference K) j)
        (sequentialDifference (sequentialHomologyTower K j))
        (sequentialProductHomologyIso K j)
        (sequentialProductHomologyIso K j)
        (homologyMap_sequentialDifference_comp_productHomologyIso K j)).hom ≫
      (sequentialLimitKernelIso
        (sequentialHomologyTower K j)).inv) ≫
      sequentialLimitToProduct (sequentialHomologyTower K j) = _
  rw [Category.assoc,
    sequentialLimitKernelIso_inv_comp_toProduct]
  dsimp only [kernel.mapIso, kernel.map]
  rw [kernel.lift_ι]

set_option backward.isDefEq.respectTransparency false in
/-- Type-stable product formula using the raw right endpoint. -/
@[reassoc]
theorem sequentialMilnorRightIso_hom_rawKernelι
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorRightIso K hK i j hij).hom ≫
        sequentialLimitToProduct (sequentialHomologyTower K j) =
      sequentialMilnorRawKernelι K hK i j hij ≫
        (sequentialProductHomologyIso K j).hom :=
  sequentialMilnorRightIso_hom_toProduct K hK i j hij

set_option backward.isDefEq.respectTransparency false in
/-- The middle object of the extracted homology window is homology of the
chosen inverse-limit complex. -/
noncomputable def sequentialMilnorMiddleIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorRawShortComplex K hK i j hij).X₂ ≅
      (limit K).homology j :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] in
@[simp]
theorem sequentialMilnorMiddleIso_hom
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorMiddleIso K hK i j hij).hom =
      𝟙 ((limit K).homology j) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] in
@[simp]
theorem sequentialMilnorMiddleIso_inv
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorMiddleIso K hK i j hij).inv =
      𝟙 ((limit K).homology j) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] in
/-- Composing the actual long-sequence boundary with the middle presentation
is the same boundary in the fixed inverse-limit homology model. -/
@[reassoc]
private theorem sequentialLimitHomologyBoundary_comp_middleIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialLimitHomologyBoundary K hK i j hij ≫
        (sequentialMilnorMiddleIso K hK i j hij).hom =
      sequentialLimitHomologyBoundary K hK i j hij :=
  Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] in
/-- The inverse middle presentation followed by the actual homology map to
the product is that same map in the fixed inverse-limit homology model. -/
@[reassoc]
private theorem sequentialMilnorMiddleIso_inv_comp_toProduct
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorMiddleIso K hK i j hij).inv ≫
        sequentialLimitHomologyToProduct K j =
      sequentialLimitHomologyToProduct K j :=
  Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical Milnor injection into homology of the inverse-limit
complex. -/
noncomputable def sequentialMilnorInjection
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialLimOne (sequentialHomologyTower K i) ⟶
      (limit K).homology j :=
  (sequentialMilnorCokernelIso K i).inv ≫
    cokernel.desc (homologyMap (sequentialDifference K) i)
      (sequentialLimitHomologyBoundary K hK i j hij)
      (homologyMap_sequentialDifference_comp_boundary K hK i j hij)

include _exactProducts in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical Milnor edge from homology of the inverse-limit complex to
the inverse limit of homology objects. The exact-product hypothesis is retained
for compatibility with the existing Milnor interface. -/
noncomputable def sequentialMilnorEdge
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (_hK : Epi (sequentialDifference K))
    (_i j : ι) (_hij : c.Rel _i j) :
    (limit K).homology j ⟶ limit (sequentialHomologyTower K j) :=
  limit.post K (homologyFunctor C c j)

omit _exactProducts in
/-- The native definition of the named edge has the actual stage homology maps as projections. -/
@[reassoc (attr := simp)]
theorem sequentialMilnorEdge_π
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) (n : ℕ) :
    sequentialMilnorEdge K hK i j hij ≫
        limit.π (sequentialHomologyTower K j) (op n) =
      homologyMap (limit.π K (op n)) j := by
  change limit.post K (homologyFunctor C c j) ≫
      limit.π (K ⋙ homologyFunctor C c j) (op n) =
    (homologyFunctor C c j).map (limit.π K (op n))
  exact limit.post_π K (homologyFunctor C c j) (op n)

omit _exactProducts in
/-- Naturality acts on the actual named edge and the actual maps of homology towers. -/
@[reassoc]
theorem sequentialMilnorEdge_naturality
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (hK : Epi (sequentialDifference K))
    (hL : Epi (sequentialDifference L))
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    homologyMap (limMap α) j ≫ sequentialMilnorEdge L hL i j hij =
      sequentialMilnorEdge K hK i j hij ≫
        limMap (sequentialHomologyTowerMap α j) := by
  exact limit.map_post α (homologyFunctor C c j)

/-- The named Milnor edge followed by the product inclusion is the actual
homology map to the product, followed by the exact-product comparison. -/
@[reassoc]
theorem sequentialMilnorEdge_toProduct
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialMilnorEdge K hK i j hij ≫
        sequentialLimitToProduct (sequentialHomologyTower K j) =
      sequentialLimitHomologyToProduct K j ≫
        (sequentialProductHomologyIso K j).hom := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc]
  change sequentialMilnorEdge K hK i j hij ≫
      sequentialLimitToProduct (sequentialHomologyTower K j) ≫
        Pi.π (fun n : ℕ => (K.obj (op n)).homology j) n =
    sequentialLimitHomologyToProduct K j ≫ (sequentialProductHomologyIso K j).hom ≫
      Pi.π (fun n : ℕ => (K.obj (op n)).homology j) n
  have hleft : sequentialMilnorEdge K hK i j hij ≫
      sequentialLimitToProduct (sequentialHomologyTower K j) ≫
        Pi.π (fun n : ℕ => (K.obj (op n)).homology j) n =
      homologyMap (limit.π K (op n)) j :=
    (congrArg (fun f : limit (sequentialHomologyTower K j) ⟶
        (K.obj (op n)).homology j => sequentialMilnorEdge K hK i j hij ≫ f)
      (sequentialLimitToProduct_π (sequentialHomologyTower K j) n)).trans
        (sequentialMilnorEdge_π K hK i j hij n)
  have hright : sequentialLimitHomologyToProduct K j ≫
      (sequentialProductHomologyIso K j).hom ≫
        Pi.π (fun n : ℕ => (K.obj (op n)).homology j) n =
      homologyMap (limit.π K (op n)) j :=
    (congrArg (fun f : (sequentialProduct K).homology j ⟶
        (K.obj (op n)).homology j => sequentialLimitHomologyToProduct K j ≫ f)
      (sequentialProductHomologyIso_hom_π K j n)).trans
        ((homologyMap_comp (sequentialLimitToProduct K)
          (Pi.π (fun n : ℕ => K.obj (op n)) n) j).symm.trans
            (congrArg (fun f : limit K ⟶ K.obj (op n) => homologyMap f j)
              (sequentialLimitToProduct_π K n)))
  exact hleft.trans hright.symm

/-- The concrete `lim¹` quotient followed by the named injection is the
actual long-sequence boundary in product-homology coordinates. -/
@[reassoc]
private theorem sequentialMilnorInjection_π_direct
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialLimOneπ (sequentialHomologyTower K i) ≫
        sequentialMilnorInjection K hK i j hij =
      (sequentialProductHomologyIso K i).inv ≫
        sequentialLimitHomologyBoundary K hK i j hij := by
  unfold sequentialMilnorInjection
  rw [sequentialMilnorCokernelIso_inv_π_assoc]
  rw [cokernel.π_desc]

set_option backward.isDefEq.respectTransparency false in
/-- The direct canonical injection is the left map transported from the
actual five-term homology window. -/
theorem sequentialMilnorInjection_eq_transported
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialMilnorInjection K hK i j hij =
      (sequentialMilnorLeftIso K hK i j hij).inv ≫
        (sequentialMilnorRawShortComplex K hK i j hij).f ≫
        (sequentialMilnorMiddleIso K hK i j hij).hom := by
  apply (cancel_epi
    (sequentialLimOneπ (sequentialHomologyTower K i))).1
  rw [sequentialMilnorInjection_π_direct]
  rw [sequentialMilnorLeftIso_inv_rawCokernelπ_early_assoc]
  rw [sequentialMilnorRawCokernelπ_f_assoc]
  apply (cancel_epi (sequentialProductHomologyIso K i).hom).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    (sequentialLimitHomologyBoundary_comp_middleIso K hK i j hij).symm

set_option backward.isDefEq.respectTransparency false in
/-- The direct canonical edge is the right map transported from the actual
five-term homology window. -/
theorem sequentialMilnorEdge_eq_transported
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialMilnorEdge K hK i j hij =
      (sequentialMilnorMiddleIso K hK i j hij).inv ≫
        (sequentialMilnorRawShortComplex K hK i j hij).g ≫
        (sequentialMilnorRightIso K hK i j hij).hom := by
  apply (cancel_mono
    (sequentialLimitToProduct (sequentialHomologyTower K j))).1
  rw [sequentialMilnorEdge_toProduct]
  rw [Category.assoc, Category.assoc,
    sequentialMilnorRightIso_hom_rawKernelι]
  symm
  calc
    (sequentialMilnorMiddleIso K hK i j hij).inv ≫
        (sequentialMilnorRawShortComplex K hK i j hij).g ≫
        sequentialMilnorRawKernelι K hK i j hij ≫
        (sequentialProductHomologyIso K j).hom =
      (sequentialMilnorMiddleIso K hK i j hij).inv ≫
        ((sequentialMilnorRawShortComplex K hK i j hij).g ≫
          sequentialMilnorRawKernelι K hK i j hij) ≫
        (sequentialProductHomologyIso K j).hom := by
      simp only [Category.assoc]
    _ = (sequentialMilnorMiddleIso K hK i j hij).inv ≫
        sequentialLimitHomologyToProduct K j ≫
          (sequentialProductHomologyIso K j).hom := by
      rw [sequentialMilnorRawShortComplex_g_rawKernelι]
    _ = sequentialLimitHomologyToProduct K j ≫
        (sequentialProductHomologyIso K j).hom := by
      rw [sequentialMilnorMiddleIso_inv_comp_toProduct_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The direct canonical injection followed by the direct canonical edge is
zero. -/
@[reassoc (attr := simp)]
theorem sequentialMilnorInjection_comp_edge
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialMilnorInjection K hK i j hij ≫
        sequentialMilnorEdge K hK i j hij = 0 := by
  rw [sequentialMilnorInjection_eq_transported,
    sequentialMilnorEdge_eq_transported]
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    (sequentialMilnorRawShortComplex K hK i j hij).zero_assoc,
    zero_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical sequential Milnor short complex in its source-facing
endpoint coordinates. -/
noncomputable def sequentialMilnorShortComplex
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) : ShortComplex C := by
  exact ShortComplex.mk
    (sequentialMilnorInjection K hK i j hij)
    (sequentialMilnorEdge K hK i j hij)
    (sequentialMilnorInjection_comp_edge K hK i j hij)

/-- The left object is concrete sequential `lim¹` of the preceding homology
tower. -/
@[simp]
theorem sequentialMilnorShortComplex_X₁
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).X₁ =
      sequentialLimOne (sequentialHomologyTower K i) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The middle object is homology of the chosen inverse-limit complex. -/
@[simp]
theorem sequentialMilnorShortComplex_X₂
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).X₂ =
      (limit K).homology j :=
  rfl

/-- The right object is the chosen inverse limit of the current homology
tower. -/
@[simp]
theorem sequentialMilnorShortComplex_X₃
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).X₃ =
      limit (sequentialHomologyTower K j) :=
  rfl

/-- The Milnor injection is the actual long-homology-sequence boundary,
factored through the concrete `lim¹` endpoint. -/
theorem sequentialMilnorShortComplex_f
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).f =
      sequentialMilnorInjection K hK i j hij :=
  rfl

/-- The Milnor edge is the actual homology map of the limit-to-product map,
factored through the kernel and the chosen inverse limit of homologies. -/
theorem sequentialMilnorShortComplex_g
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).g =
      sequentialMilnorEdge K hK i j hij :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The raw homology window and the canonical Milnor short complex are
canonically isomorphic. -/
noncomputable def sequentialMilnorShortComplexIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialMilnorRawShortComplex K hK i j hij ≅
      sequentialMilnorShortComplex K hK i j hij := by
  let S := sequentialMilnorRawShortComplex K hK i j hij
  let M := sequentialMilnorShortComplex K hK i j hij
  let e₁ : S.X₁ ≅ M.X₁ := sequentialMilnorLeftIso K hK i j hij
  let e₂ : S.X₂ ≅ M.X₂ := sequentialMilnorMiddleIso K hK i j hij
  let e₃ : S.X₃ ≅ M.X₃ := sequentialMilnorRightIso K hK i j hij
  exact ShortComplex.isoMk e₁ e₂ e₃
    (by
      rw [sequentialMilnorShortComplex_f,
        sequentialMilnorInjection_eq_transported]
      exact e₁.hom_inv_id_assoc (S.f ≫ e₂.hom))
    (by
      rw [sequentialMilnorShortComplex_g,
        sequentialMilnorEdge_eq_transported]
      exact e₂.hom_inv_id_assoc (S.g ≫ e₃.hom))

/-- The canonical sequential Milnor short complex is short exact. -/
theorem sequentialMilnorShortComplex_shortExact
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).ShortExact :=
  ShortComplex.shortExact_of_iso
    (sequentialMilnorShortComplexIso K hK i j hij)
    (sequentialMilnorRawShortComplex_shortExact K hK i j hij)

/-- Inverse form of the left endpoint characteristic equation. -/
@[reassoc]
theorem sequentialMilnorLeftIso_inv_π
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialLimOneπ (sequentialHomologyTower K i) ≫
        (sequentialMilnorLeftIso K hK i j hij).inv =
      (sequentialProductHomologyIso K i).inv ≫
        cokernel.π (homologyMap (sequentialDifference K) i) :=
  sequentialMilnorLeftIso_inv_π_early K hK i j hij

set_option backward.isDefEq.respectTransparency false in
/-- The inverse endpoint transport identifies the concrete `lim¹` quotient
with the raw cokernel quotient in product-homology coordinates. -/
@[reassoc]
theorem sequentialMilnorLeftIso_inv_rawCokernelπ
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialLimOneπ (sequentialHomologyTower K i) ≫
        (sequentialMilnorLeftIso K hK i j hij).inv =
      (sequentialProductHomologyIso K i).inv ≫
        sequentialMilnorRawCokernelπ K hK i j hij :=
  sequentialMilnorLeftIso_inv_π K hK i j hij

/-- The concrete `lim¹` quotient followed by the named Milnor injection is
the actual long-homology-sequence boundary in product-homology coordinates. -/
@[reassoc]
theorem sequentialMilnorInjection_π
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialLimOneπ (sequentialHomologyTower K i) ≫
        sequentialMilnorInjection K hK i j hij =
      (sequentialProductHomologyIso K i).inv ≫
        sequentialLimitHomologyBoundary K hK i j hij :=
  sequentialMilnorInjection_π_direct K hK i j hij

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the named Milnor injection under a map of inverse towers. -/
@[reassoc]
theorem sequentialMilnorInjection_naturality
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (hK : Epi (sequentialDifference K))
    (hL : Epi (sequentialDifference L))
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    sequentialLimOneMap (sequentialHomologyTowerMap α i) ≫
        sequentialMilnorInjection L hL i j hij =
      sequentialMilnorInjection K hK i j hij ≫
        homologyMap (limMap α) j := by
  apply (cancel_epi
    (sequentialLimOneπ (sequentialHomologyTower K i))).1
  rw [sequentialLimOneπ_comp_map_assoc]
  rw [sequentialMilnorInjection_π]
  rw [sequentialProductHomologyIso_inv_naturality_assoc]
  rw [sequentialMilnorInjection_π_assoc]
  apply (cancel_epi (sequentialProductHomologyIso K i).hom).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    (sequentialLimitBoundary_naturality hK hL α i j hij).symm

set_option backward.isDefEq.respectTransparency false in
/-- The Milnor edge followed by the canonical inclusion into the sequential
product is the homology map of the actual limit-to-product morphism, followed
by the exact-product comparison. -/
@[reassoc]
theorem sequentialMilnorShortComplex_g_toProduct
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).g ≫
        sequentialLimitToProduct (sequentialHomologyTower K j) =
      homologyMap (sequentialLimitToProduct K) j ≫
        (sequentialProductHomologyIso K j).hom := by
  rw [sequentialMilnorShortComplex_g,
    sequentialMilnorEdge_toProduct,
    sequentialLimitHomologyToProduct_eq]

set_option backward.isDefEq.respectTransparency false in
/-- Every stage projection of the Milnor edge is the homology map of the
corresponding projection from the inverse-limit complex. -/
@[reassoc (attr := simp)]
theorem sequentialMilnorShortComplex_g_π
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) (n : ℕ) :
    (sequentialMilnorShortComplex K hK i j hij).g ≫
        limit.π (sequentialHomologyTower K j) (op n) =
      homologyMap (limit.π K (op n)) j := by
  simpa only [sequentialMilnorShortComplex_X₂, sequentialMilnorShortComplex_g] using
    sequentialMilnorEdge_π K hK i j hij n

set_option backward.isDefEq.respectTransparency false in
/-- The middle map induced by a map of towers is the actual homology map of
the canonical map between inverse-limit complexes. -/
noncomputable def sequentialMilnorMiddleMap
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (hK : Epi (sequentialDifference K))
    (hL : Epi (sequentialDifference L))
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).X₂ ⟶
      (sequentialMilnorShortComplex L hL i j hij).X₂ :=
  homologyMap (limMap α) j

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the actual left map of the canonical Milnor short complex. -/
@[reassoc]
theorem sequentialMilnorShortComplex_f_naturality
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (hK : Epi (sequentialDifference K))
    (hL : Epi (sequentialDifference L))
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    sequentialLimOneMap (sequentialHomologyTowerMap α i) ≫
        (sequentialMilnorShortComplex L hL i j hij).f =
      (sequentialMilnorShortComplex K hK i j hij).f ≫
        sequentialMilnorMiddleMap hK hL α i j hij := by
  rw [sequentialMilnorShortComplex_f,
    sequentialMilnorShortComplex_f]
  unfold sequentialMilnorMiddleMap
  exact sequentialMilnorInjection_naturality hK hL α i j hij

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the Milnor edge under a map of inverse towers. -/
@[reassoc]
theorem sequentialMilnorShortComplex_g_naturality
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (hK : Epi (sequentialDifference K))
    (hL : Epi (sequentialDifference L))
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    sequentialMilnorMiddleMap hK hL α i j hij ≫
        (sequentialMilnorShortComplex L hL i j hij).g =
      (sequentialMilnorShortComplex K hK i j hij).g ≫
        limMap (sequentialHomologyTowerMap α j) := by
  simpa only [sequentialMilnorMiddleMap, sequentialMilnorShortComplex_X₂,
    sequentialMilnorShortComplex_g] using
      sequentialMilnorEdge_naturality hK hL α i j hij

/-- A map of inverse towers induces a morphism of the actual canonical
Milnor short complexes. -/
noncomputable def sequentialMilnorShortComplexMap
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (hK : Epi (sequentialDifference K))
    (hL : Epi (sequentialDifference L))
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    sequentialMilnorShortComplex K hK i j hij ⟶
      sequentialMilnorShortComplex L hL i j hij where
  τ₁ := sequentialLimOneMap (sequentialHomologyTowerMap α i)
  τ₂ := sequentialMilnorMiddleMap hK hL α i j hij
  τ₃ := limMap (sequentialHomologyTowerMap α j)
  comm₁₂ := sequentialMilnorShortComplex_f_naturality hK hL α i j hij
  comm₂₃ := sequentialMilnorShortComplex_g_naturality hK hL α i j hij

@[simp]
theorem sequentialMilnorShortComplexMap_τ₁
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (hK : Epi (sequentialDifference K))
    (hL : Epi (sequentialDifference L))
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplexMap hK hL α i j hij).τ₁ =
      sequentialLimOneMap (sequentialHomologyTowerMap α i) :=
  rfl

@[simp]
theorem sequentialMilnorShortComplexMap_τ₂
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (hK : Epi (sequentialDifference K))
    (hL : Epi (sequentialDifference L))
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplexMap hK hL α i j hij).τ₂ =
      homologyMap (limMap α) j :=
  rfl

@[simp]
theorem sequentialMilnorShortComplexMap_τ₃
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (hK : Epi (sequentialDifference K))
    (hL : Epi (sequentialDifference L))
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplexMap hK hL α i j hij).τ₃ =
      limMap (sequentialHomologyTowerMap α j) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The induced morphism of Milnor short complexes preserves identities. -/
@[simp]
theorem sequentialMilnorShortComplexMap_id
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    sequentialMilnorShortComplexMap hK hK (𝟙 K) i j hij =
      𝟙 (sequentialMilnorShortComplex K hK i j hij) := by
  ext
  · change sequentialLimOneMap (sequentialHomologyTowerMap (𝟙 K) i) = 𝟙 _
    rw [sequentialHomologyTowerMap_id,
      sequentialLimOneMap_id]
  · have hlim : limMap (𝟙 K) = 𝟙 (limit K) := by
      apply limit.hom_ext
      intro n
      simp
    change homologyMap (limMap (𝟙 K)) j = 𝟙 _
    rw [hlim, homologyMap_id]
  · have hlim : limMap (𝟙 (sequentialHomologyTower K j)) =
        𝟙 (limit (sequentialHomologyTower K j)) := by
      apply limit.hom_ext
      intro n
      simp
    change limMap (sequentialHomologyTowerMap (𝟙 K) j) = 𝟙 _
    rw [sequentialHomologyTowerMap_id]
    exact hlim

set_option backward.isDefEq.respectTransparency false in
/-- The induced morphism of Milnor short complexes preserves composition. -/
@[reassoc]
theorem sequentialMilnorShortComplexMap_comp
    {K L M : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (hK : Epi (sequentialDifference K))
    (hL : Epi (sequentialDifference L))
    (hM : Epi (sequentialDifference M))
    (α : K ⟶ L) (β : L ⟶ M)
    (i j : ι) (hij : c.Rel i j) :
    sequentialMilnorShortComplexMap hK hM (α ≫ β) i j hij =
      sequentialMilnorShortComplexMap hK hL α i j hij ≫
        sequentialMilnorShortComplexMap hL hM β i j hij := by
  ext
  · change
      sequentialLimOneMap (sequentialHomologyTowerMap (α ≫ β) i) =
        sequentialLimOneMap (sequentialHomologyTowerMap α i) ≫
          sequentialLimOneMap (sequentialHomologyTowerMap β i)
    rw [sequentialHomologyTowerMap_comp,
      sequentialLimOneMap_comp]
  · have hlim : limMap (α ≫ β) = limMap α ≫ limMap β := by
      apply limit.hom_ext
      intro n
      simp
    change homologyMap (limMap (α ≫ β)) j =
      homologyMap (limMap α) j ≫ homologyMap (limMap β) j
    rw [hlim, homologyMap_comp]
  · change limMap (sequentialHomologyTowerMap (α ≫ β) j) =
      limMap (sequentialHomologyTowerMap α j) ≫
        limMap (sequentialHomologyTowerMap β j)
    rw [sequentialHomologyTowerMap_comp]
    apply limit.hom_ext
    intro n
    simp

end HomologicalComplex

end
