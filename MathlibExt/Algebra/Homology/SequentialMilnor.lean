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
# Milnor sequences for sequential inverse towers

Let C be an abelian category, c an arbitrary complex shape, and
K=(⋯ → K₂ → K₁ → K₀) an inverse tower of complexes. Write
P(K)=∏ₙKₙ and Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁).
When C has sequential inverse limits and Δ_K is epic, the sequence
0 → lim K → P(K) —Δ_K→ P(K) → 0 is short exact.

If countable products in C are exact, homology commutes with P.
For every c.Rel(i,j), the resulting canonical Milnor sequence is
0 → lim¹(H_iK) → H_j(lim K) → lim(H_jK) → 0,
where lim¹ is the concrete cokernel of the homology-tower difference.
The injection is induced by the long-sequence boundary, and the edge
has stage projections H_j(lim K → Kₙ). The sequence is natural in tower
maps. Degreewise epic differences suffice for Δ_K to be epic; for abelian
groups, degreewise Mittag–Leffler towers provide this condition.
The category object, morphism and complex-index universes are independent.
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
/-- Let C be abelian with countable products and c any complex shape.

Countable products of complexes of shape c exist and are computed in every degree by the corresponding product in C. -/
noncomputable instance homologicalComplexHasCountableProducts :
    HasCountableProducts (HomologicalComplex C c) where
  out _ := inferInstance

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c.

For a degree i, the inverse homology tower H_iK has object H_i(Kₙ) at stage n and transition maps induced on homology by the transitions of K. -/
abbrev sequentialHomologyTower
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) : ℕᵒᵖ ⥤ C where
  obj n := (K.obj n).homology i
  map f := (K ⋙ homologyFunctor C c i).map f
  map_id n := (K ⋙ homologyFunctor C c i).map_id n
  map_comp f g := (K ⋙ homologyFunctor C c i).map_comp f g

omit [HasCountableProducts C] [CountableAB4Star C] [HasLimitsOfShape ℕᵒᵖ C] in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c.

The degree-i homology tower equals the composite of K with the homology functor H_i on complexes of shape c. -/
theorem sequentialHomologyTower_eq_comp
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) :
    sequentialHomologyTower K i = K ⋙ homologyFunctor C c i := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume countable products in C are exact.
Write P(K)=∏ₙKₙ, H_iK for the tower (H_i(Kₙ))ₙ and
β_i:H_i(P(K)) ≅ P(H_iK) for the canonical product comparison.

The canonical isomorphism β_i:H_i(P(K)) ≅ P(H_iK) identifies the homology of the product complex with the product of homology objects. -/
noncomputable def sequentialProductHomologyIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) :
    (sequentialProduct K).homology i ≅
      sequentialProduct (sequentialHomologyTower K i) :=
  PreservesProduct.iso (homologyFunctor C c i)
    (fun n : ℕ => K.obj (op n))

set_option backward.isDefEq.respectTransparency false in
omit [HasLimitsOfShape ℕᵒᵖ C] in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume countable products in C are exact.
Write P(K)=∏ₙKₙ, H_iK for the tower (H_i(Kₙ))ₙ and
β_i:H_i(P(K)) ≅ P(H_iK) for the canonical product comparison.

For every stage n, the n-th projection of β_i is H_i of the product projection P(K) → Kₙ. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume countable products in C are exact.
Write P(K)=∏ₙKₙ, H_iK for the tower (H_i(Kₙ))ₙ and
β_i:H_i(P(K)) ≅ P(H_iK) for the canonical product comparison.

For Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁), the comparison intertwines differences: β_i ∘ H_i(Δ_K)=Δ_{H_iK} ∘ β_i. -/
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

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c.

Evaluation at degree i gives the inverse tower with objects Kₙᵢ and transitions the degree-i components of the tower maps. -/
abbrev sequentialDegreeTower
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) : ℕᵒᵖ ⥤ C :=
  K ⋙ eval C c i

omit [CountableAB4Star C] [HasLimitsOfShape ℕᵒᵖ C] in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products.
Write P(K)=∏ₙKₙ and Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁), where tₙ:Kₙ₊₁ → Kₙ
is the adjacent transition.

For each degree i, the canonical isomorphism ε_i:P(K)ᵢ ≅ ∏ₙKₙᵢ compares evaluation of the product complex with the product of the evaluated tower. -/
noncomputable def sequentialProductEvalIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) :
    (sequentialProduct K).X i ≅
      sequentialProduct (sequentialDegreeTower K i) :=
  PreservesProduct.iso (eval C c i) (fun n : ℕ => K.obj (op n))

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] [HasLimitsOfShape ℕᵒᵖ C] in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products.
Write P(K)=∏ₙKₙ and Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁), where tₙ:Kₙ₊₁ → Kₙ
is the adjacent transition.

For the comparison ε_i:P(K)ᵢ ≅ ∏ₙKₙᵢ, its n-th projection is the degree-i component of the product projection P(K) → Kₙ. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products.
Write P(K)=∏ₙKₙ and Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁), where tₙ:Kₙ₊₁ → Kₙ
is the adjacent transition.

Under ε_i:P(K)ᵢ ≅ P((Kₙᵢ)ₙ), the component of the complex difference satisfies ε_i ∘ (Δ_K)ᵢ=Δ_{(Kₙᵢ)} ∘ ε_i. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products.
Write P(K)=∏ₙKₙ and Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁), where tₙ:Kₙ₊₁ → Kₙ
is the adjacent transition.

If the standard difference on the evaluated tower (Kₙᵢ)ₙ is epic for every i, then Δ_K is an epimorphism of complexes. -/
theorem epi_sequentialDifference_of_epi_degreewise
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (h : ∀ i : ι, Epi
      (sequentialDifference (sequentialDegreeTower K i))) :
    Epi (sequentialDifference K) := by
  apply epi_of_epi_f
  intro i
  exact (epi_map_sequentialDifference_iff (eval C c i) K).2 (h i)

/-- Let K be an inverse tower of complexes of any shape c in abelian groups.

If, in each degree i and each fixed stage n, the images of later stages in Kₙᵢ eventually stabilize, then the product difference Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic. -/
theorem _root_.AddCommGrpCat.epi_sequentialDifference_of_degreewise_isMittagLeffler
    (K : ℕᵒᵖ ⥤ HomologicalComplex AddCommGrpCat.{u} c)
    (h : ∀ i : ι,
      (sequentialDegreeTower K i).IsSequentialMittagLeffler) :
    Epi (sequentialDifference K) :=
  epi_sequentialDifference_of_epi_degreewise K fun i =>
    AddCommGrpCat.epi_sequentialDifference_of_isMittagLeffler _ (h i)

/-- Let C be abelian, c any complex shape and α:K → L a map of inverse towers of complexes.

The induced map H_iK → H_iL has stage-n component H_i(αₙ). -/
abbrev sequentialHomologyTowerMap
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c} (α : K ⟶ L) (i : ι) :
    sequentialHomologyTower K i ⟶ sequentialHomologyTower L i :=
  Functor.whiskerRight α (homologyFunctor C c i)

omit [HasCountableProducts C] [CountableAB4Star C]
  [HasLimitsOfShape ℕᵒᵖ C] in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c.

The map of degree-i homology towers induced by 1_K is the identity of H_iK. -/
theorem sequentialHomologyTowerMap_id
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) :
    sequentialHomologyTowerMap (𝟙 K) i =
      𝟙 (sequentialHomologyTower K i) := by
  exact Functor.whiskerRight_id' (homologyFunctor C c i)

omit [HasCountableProducts C] [CountableAB4Star C]
  [HasLimitsOfShape ℕᵒᵖ C] in
/-- Let C be abelian, c any complex shape and α:K → L, β:L → M maps of inverse towers.

The homology tower map of β∘α equals H_i(β)∘H_i(α). -/
@[reassoc]
theorem sequentialHomologyTowerMap_comp
    {K L M : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (α : K ⟶ L) (β : L ⟶ M) (i : ι) :
    sequentialHomologyTowerMap (α ≫ β) i =
      sequentialHomologyTowerMap α i ≫
        sequentialHomologyTowerMap β i := by
  exact Functor.whiskerRight_comp α β (homologyFunctor C c i)

omit [HasLimitsOfShape ℕᵒᵖ C] in
/-- Let C be abelian with exact countable products and c any complex shape.
For towers K,L and α:K → L, let P(α) be the product map and
H_a(α) the map of degree-a homology towers.

The product homology comparisons satisfy β_L,i ∘ H_i(P(α))=P(H_i(α)) ∘ β_K,i. -/
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
/-- Let C be abelian with exact countable products and c any complex shape.
For towers K,L and α:K → L, let P(α) be the product map and
H_a(α) the map of degree-a homology towers.

The inverse comparisons satisfy β_L,i⁻¹ ∘ P(H_i(α))=H_i(P(α)) ∘ β_K,i⁻¹. -/
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
/-- Let C be abelian with countable products and sequential inverse limits, c any complex shape, and α:K → L a tower map.

The induced map between lim K → P(K) → P(K) and lim L → P(L) → P(L) has components lim(α), P(α), P(α), and commutes with the inclusions and differences. -/
noncomputable def sequentialLimitShortComplexMap
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c} (α : K ⟶ L) :
    sequentialLimitShortComplex K ⟶ sequentialLimitShortComplex L where
  τ₁ := limMap α
  τ₂ := sequentialProductMap α
  τ₃ := sequentialProductMap α
  comm₁₂ := (sequentialLimitToProduct_naturality α).symm
  comm₂₃ := sequentialDifference_naturality α

omit [CountableAB4Star C] in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products.
Write P(K)=∏ₙKₙ and Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁), where tₙ:Kₙ₊₁ → Kₙ
is the adjacent transition. Assume sequential inverse limits exist in C.

If Δ_K is epic, then 0 → lim K → P(K) —Δ_K→ P(K) → 0 is short exact. -/
theorem sequentialLimitShortComplex_shortExact_of_epi
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K)) :
    (sequentialLimitShortComplex K).ShortExact := by
  exact ShortComplex.ShortExact.mk'
    (sequentialLimitShortComplex_exact K) inferInstance hK

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

The connecting map δ:H_i(P(K)) → H_j(lim K) in the homology sequence of the short exact limit-product-difference sequence. -/
noncomputable def sequentialLimitHomologyBoundary
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialProduct K).homology i ⟶ (limit K).homology j :=
  (sequentialLimitShortComplex_shortExact_of_epi K hK).δ i j hij

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products.
Write P(K)=∏ₙKₙ and Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁), where tₙ:Kₙ₊₁ → Kₙ
is the adjacent transition. Assume sequential inverse limits exist in C.

The map H_j(lim K) → H_j(P(K)) induced by the canonical inclusion lim K → P(K). -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products.
Write P(K)=∏ₙKₙ and Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁), where tₙ:Kₙ₊₁ → Kₙ
is the adjacent transition. Assume sequential inverse limits exist in C.

The homology map of lim K → P(K), followed by H_j(Δ_K), is zero. -/
@[reassoc (attr := simp)]
theorem sequentialLimitHomologyToProduct_comp_difference
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (j : ι) :
    homologyMap (sequentialLimitToProduct K) j ≫
        homologyMap (sequentialDifference K) j = 0 := by
  rw [← homologyMap_comp,
    sequentialLimitToProduct_comp_difference, homologyMap_zero]

set_option backward.isDefEq.respectTransparency false in
omit [CountableAB4Star C] in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

The boundary and inclusion maps satisfy ρ∘δ=0. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

The product-difference homology map satisfies δ∘H_i(Δ_K)=0. -/
@[reassoc (attr := simp)]
theorem homologyMap_sequentialDifference_comp_boundary
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    homologyMap (sequentialDifference K) i ≫
        sequentialLimitHomologyBoundary K hK i j hij = 0 :=
  (sequentialLimitShortComplex_shortExact_of_epi K hK).comp_δ i j hij

omit [CountableAB4Star C] in
/-- Let C be abelian with countable products and sequential inverse limits, c any complex shape, and α:K → L a tower map. Assume Δ_K and Δ_L are epic and c.Rel(i,j).

The boundaries satisfy H_j(lim α) ∘ δ_K=δ_L ∘ H_i(P(α)). -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

The five-term homology window is H_i(P(K)) —H_i(Δ_K)→ H_i(P(K)) —δ→ H_j(lim K) —ρ→ H_j(P(K)) —H_j(Δ_K)→ H_j(P(K)). -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

The five-term sequence H_i(P(K)) → H_i(P(K)) → H_j(lim K) → H_j(P(K)) → H_j(P(K)), with maps H_i(Δ_K),δ,ρ,H_j(Δ_K), is exact. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

The extracted short complex has terms Coker(H_i(Δ_K)), H_j(lim K), Ker(H_j(Δ_K)); its first map is induced by δ and its second is the factorization of ρ through the kernel. -/
noncomputable def sequentialMilnorRawShortComplex
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) : ShortComplex C :=
  ComposableArrows.exactSequenceFourShortComplex
    (sequentialMilnorHomologyWindow K hK i j hij)
    (sequentialMilnorHomologyWindow_exact K hK i j hij)

omit [CountableAB4Star C] in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

The extracted sequence 0 → Coker(H_i(Δ_K)) → H_j(lim K) → Ker(H_j(Δ_K)) → 0 is short exact. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

For the quotient q:H_i(P(K)) → Coker(H_i(Δ_K)) and the left map f of the extracted sequence, f∘q=δ. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

For the right map g:H_j(lim K) → Ker(H_j(Δ_K)) of the extracted sequence and kernel inclusion κ, κ∘g=ρ. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

The quotient H_i(P(K)) → Coker(H_i(Δ_K)), regarded as a map into the left term of the extracted Milnor sequence. -/
noncomputable def sequentialMilnorRawCokernelπ
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialProduct K).homology i ⟶
      (sequentialMilnorRawShortComplex K hK i j hij).X₁ :=
  cokernel.π (homologyMap (sequentialDifference K) i)

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

The inclusion Ker(H_j(Δ_K)) → H_j(P(K)), regarded as a map from the right term of the extracted Milnor sequence. -/
noncomputable def sequentialMilnorRawKernelι
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorRawShortComplex K hK i j hij).X₃ ⟶
      (sequentialProduct K).homology j :=
  kernel.ι (homologyMap (sequentialDifference K) j)

omit [CountableAB4Star C] in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

The quotient into the extracted left term, followed by its injection into the middle term H_j(lim K), equals δ. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

The right map of the extracted Milnor sequence, followed by the inclusion of its right term into H_j(P(K)), equals ρ. -/
@[reassoc]
theorem sequentialMilnorRawShortComplex_g_rawKernelι
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorRawShortComplex K hK i j hij).g ≫
        sequentialMilnorRawKernelι K hK i j hij =
      sequentialLimitHomologyToProduct K j :=
  sequentialMilnorRawShortComplex_g_ι K hK i j hij

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume countable products in C are exact.
Write P(K)=∏ₙKₙ, H_iK for the tower (H_i(Kₙ))ₙ and
β_i:H_i(P(K)) ≅ P(H_iK) for the canonical product comparison.

The isomorphism Coker(H_i(Δ_K)) ≅ lim¹(H_iK) induced by β_i and its difference-intertwining equation, where lim¹(H_iK)=Coker(Δ_{H_iK}). -/
noncomputable def sequentialMilnorCokernelIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (i : ι) :
    cokernel (homologyMap (sequentialDifference K) i) ≅
      sequentialLimOne (sequentialHomologyTower K i) :=
  sequentialDifferenceCokernelIso (homologyFunctor C c i) K

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume countable products in C are exact.
Write P(K)=∏ₙKₙ, H_iK for the tower (H_i(Kₙ))ₙ and
β_i:H_i(P(K)) ≅ P(H_iK) for the canonical product comparison. Assume sequential inverse limits exist in C.

The isomorphism Ker(H_j(Δ_K)) ≅ lim(H_jK) identifies the kernel through β_j with the limit of the homology tower. -/
noncomputable def sequentialMilnorKernelIsoLimit
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (j : ι) :
    kernel (homologyMap (sequentialDifference K) j) ≅
      limit (sequentialHomologyTower K j) :=
  sequentialDifferenceKernelIso (homologyFunctor C c j) K ≪≫
    (sequentialLimitKernelIso (sequentialHomologyTower K j)).symm

omit [HasLimitsOfShape ℕᵒᵖ C] in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume countable products in C are exact.
Write P(K)=∏ₙKₙ, H_iK for the tower (H_i(Kₙ))ₙ and
β_i:H_i(P(K)) ≅ P(H_iK) for the canonical product comparison.

Let η_i:Coker(H_i(Δ_K)) ≅ lim¹(H_iK), q_i:P(H_iK) → lim¹(H_iK), and π_i:H_i(P(K)) → Coker(H_i(Δ_K)). Their inverse quotient formula is η_i⁻¹ ∘ q_i=π_i ∘ β_i⁻¹. -/
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

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume countable products in C are exact.
Write P(K)=∏ₙKₙ, H_iK for the tower (H_i(Kₙ))ₙ and
β_i:H_i(P(K)) ≅ P(H_iK) for the canonical product comparison. Assume sequential inverse limits exist in C.

Let ζ_j:Ker(H_j(Δ_K)) ≅ lim(H_jK), κ_j its kernel inclusion, and ℓ_j:lim(H_jK) → P(H_jK) the product inclusion. Then ℓ_j ∘ ζ_j=β_j ∘ κ_j. -/
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

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

For the extracted sequence R with terms Coker(H_i(Δ_K)), H_j(lim K), Ker(H_j(Δ_K)), the left-term isomorphism λ:R₁ ≅ lim¹(H_iK) induced by β_i. -/
noncomputable def sequentialMilnorLeftIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorRawShortComplex K hK i j hij).X₁ ≅
      sequentialLimOne (sequentialHomologyTower K i) := by
  change cokernel (homologyMap (sequentialDifference K) i) ≅ _
  exact sequentialMilnorCokernelIso K i

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

For the extracted sequence R with terms Coker(H_i(Δ_K)), H_j(lim K), Ker(H_j(Δ_K)), the right-term isomorphism ζ:R₃ ≅ lim(H_jK) induced by β_j. -/
noncomputable def sequentialMilnorRightIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorRawShortComplex K hK i j hij).X₃ ≅
      limit (sequentialHomologyTower K j) := by
  change kernel (homologyMap (sequentialDifference K) j) ≅ _
  exact sequentialMilnorKernelIsoLimit K j

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

Let λ:Coker(H_i(Δ_K)) ≅ lim¹(H_iK), π_i the cokernel projection and q_i:P(H_iK) → lim¹(H_iK). The quotient formula is λ ∘ π_i=q_i ∘ β_i. -/
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

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

For the left-term isomorphism λ, the inverse quotient formula is λ⁻¹ ∘ q_i=π_i ∘ β_i⁻¹, where q_i is the concrete lim¹ projection and π_i is the homology-difference cokernel projection. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

Let q_R:H_i(P(K)) → R₁ be the quotient into the extracted left term and λ:R₁ ≅ lim¹(H_iK). Then λ⁻¹ ∘ q_i=q_R ∘ β_i⁻¹. -/
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

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

For the right-term isomorphism ζ:Ker(H_j(Δ_K)) ≅ lim(H_jK), its composite with the homology-limit product inclusion ℓ_j is β_j followed after the kernel inclusion κ_j: ℓ_j∘ζ=β_j∘κ_j. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

Let κ_R:R₃ → H_j(P(K)) be the inclusion from the extracted right term and ζ:R₃ ≅ lim(H_jK). For the product inclusion ℓ_j, the right-term coordinate formula is ℓ_j∘ζ=β_j∘κ_R. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The canonical identification μ:R₂ ≅ H_j(lim K) of the middle term of the extracted kernel-cokernel sequence with homology of the inverse-limit complex. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

Under the canonical middle-term identification μ:R₂ ≅ H_j(lim K), the long-sequence boundary is unchanged: μ∘δ=δ. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has countable products and sequential inverse limits,
Δ_K:P(K) → P(K), with coordinates xₙ−tₙ(xₙ₊₁), is epic, and c.Rel(i,j).
Let δ:H_i(P(K)) → H_j(lim K) and ρ:H_j(lim K) → H_j(P(K)) be the
boundary and inclusion maps for 0 → lim K → P(K) —Δ_K→ P(K) → 0.

For the canonical middle-term identification μ:R₂ ≅ H_j(lim K), its inverse leaves the limit-to-product homology map unchanged: ρ∘μ⁻¹=ρ. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The Milnor injection I:lim¹(H_iK) → H_j(lim K) induced by the boundary δ through the homology-difference cokernel. It is characterized by I∘q_i=δ∘β_i⁻¹, where q_i:P(H_iK) → lim¹(H_iK) is the quotient. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The Milnor edge E:H_j(lim K) → lim(H_jK) is induced by the maps H_j(lim K → Kₙ). These are its composites with the stage projections of the inverse limit. -/
noncomputable def sequentialMilnorEdge
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (_hK : Epi (sequentialDifference K))
    (_i j : ι) (_hij : c.Rel _i j) :
    (limit K).homology j ⟶ limit (sequentialHomologyTower K j) :=
  limit.post K (homologyFunctor C c j)

omit _exactProducts in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

For the Milnor edge E and every stage n, the stage projection satisfies π_n∘E=H_j(lim K → Kₙ). -/
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
/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape, and K,L inverse towers of complexes.
Assume their product differences Δ(x)ₙ=xₙ−tₙ(xₙ₊₁) are epic and c.Rel(i,j).
Let α:K → L be a tower map.

The Milnor edges satisfy E_L∘H_j(lim α)=lim(H_jα)∘E_K. -/
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

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

For the edge E and the product inclusion ℓ_j:lim(H_jK) → P(H_jK), the product formula is ℓ_j∘E=β_j∘H_j(lim K → P(K)). -/
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

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

For the Milnor injection I, concrete lim¹ quotient q_i and long-sequence boundary δ, the quotient equation is I∘q_i=δ∘β_i⁻¹. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

Let R be the extracted sequence, λ:R₁ ≅ lim¹(H_iK) its left-term comparison and μ:R₂ ≅ H_j(lim K) its middle comparison. The canonical injection is I=μ∘R.f∘λ⁻¹. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

Let R be the extracted sequence, μ:R₂ ≅ H_j(lim K) and ζ:R₃ ≅ lim(H_jK) its middle and right comparisons. The canonical edge is E=ζ∘R.g∘μ⁻¹. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The composite of the canonical injection I:lim¹(H_iK) → H_j(lim K) with the canonical edge E:H_j(lim K) → lim(H_jK) is zero: E∘I=0. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The canonical short complex is lim¹(H_iK) —I→ H_j(lim K) —E→ lim(H_jK), with the boundary-induced injection and the stage-projection edge. -/
noncomputable def sequentialMilnorShortComplex
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) : ShortComplex C := by
  exact ShortComplex.mk
    (sequentialMilnorInjection K hK i j hij)
    (sequentialMilnorEdge K hK i j hij)
    (sequentialMilnorInjection_comp_edge K hK i j hij)

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The left term of the canonical Milnor short complex is the concrete lim¹ object Coker(Δ_{H_iK}). -/
@[simp]
theorem sequentialMilnorShortComplex_X₁
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).X₁ =
      sequentialLimOne (sequentialHomologyTower K i) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The middle term of the canonical Milnor short complex is H_j(lim K). -/
@[simp]
theorem sequentialMilnorShortComplex_X₂
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).X₂ =
      (limit K).homology j :=
  rfl

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The right term of the canonical Milnor short complex is lim(H_jK). -/
@[simp]
theorem sequentialMilnorShortComplex_X₃
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).X₃ =
      limit (sequentialHomologyTower K j) :=
  rfl

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The first map of the canonical Milnor short complex is the injection lim¹(H_iK) → H_j(lim K) induced by the long-sequence boundary. -/
theorem sequentialMilnorShortComplex_f
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).f =
      sequentialMilnorInjection K hK i j hij :=
  rfl

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The second map of the canonical Milnor short complex is the edge H_j(lim K) → lim(H_jK), whose stage projections are H_j(lim K → Kₙ). -/
theorem sequentialMilnorShortComplex_g
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).g =
      sequentialMilnorEdge K hK i j hij :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The extracted sequence Coker(H_iΔ_K) → H_j(lim K) → Ker(H_jΔ_K) is canonically isomorphic to the Milnor sequence lim¹(H_iK) → H_j(lim K) → lim(H_jK), through the endpoint comparisons. -/
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

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The canonical sequence 0 → lim¹(H_iK) —I→ H_j(lim K) —E→ lim(H_jK) → 0 is short exact. -/
theorem sequentialMilnorShortComplex_shortExact
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c)
    (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).ShortExact :=
  ShortComplex.shortExact_of_iso
    (sequentialMilnorShortComplexIso K hK i j hij)
    (sequentialMilnorRawShortComplex_shortExact K hK i j hij)

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

Let λ:Coker(H_iΔ_K) ≅ lim¹(H_iK), π_i:H_i(P(K)) → Coker(H_iΔ_K) and q_i:P(H_iK) → lim¹(H_iK). Then λ⁻¹∘q_i=π_i∘β_i⁻¹. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

For λ:R₁ ≅ lim¹(H_iK) and the quotient q_R:H_i(P(K)) → R₁ into the extracted left term, λ⁻¹∘q_i=q_R∘β_i⁻¹, where q_i is the concrete lim¹ quotient. -/
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

/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The quotient q_i:P(H_iK) → lim¹(H_iK) followed by the named injection I equals the boundary δ in product-homology coordinates: I∘q_i=δ∘β_i⁻¹. -/
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
/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape, and K,L inverse towers of complexes.
Assume their product differences Δ(x)ₙ=xₙ−tₙ(xₙ₊₁) are epic and c.Rel(i,j).
Let α:K → L be a tower map.

The canonical injections satisfy I_L∘lim¹(H_iα)=H_j(lim α)∘I_K. -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The right map g of the canonical Milnor short complex satisfies ℓ_j∘g=β_j∘H_j(lim K → P(K)), where ℓ_j:lim(H_jK) → P(H_jK). -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

For every stage n, the right map g of the canonical Milnor short complex satisfies π_n∘g=H_j(lim K → Kₙ). -/
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
/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape, and K,L inverse towers of complexes.
Assume their product differences Δ(x)ₙ=xₙ−tₙ(xₙ₊₁) are epic and c.Rel(i,j).
Let α:K → L be a tower map.

The middle map between the two canonical Milnor sequences is H_j(lim α):H_j(lim K) → H_j(lim L). -/
noncomputable def sequentialMilnorMiddleMap
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (hK : Epi (sequentialDifference K))
    (hL : Epi (sequentialDifference L))
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorShortComplex K hK i j hij).X₂ ⟶
      (sequentialMilnorShortComplex L hL i j hij).X₂ :=
  homologyMap (limMap α) j

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape, and K,L inverse towers of complexes.
Assume their product differences Δ(x)ₙ=xₙ−tₙ(xₙ₊₁) are epic and c.Rel(i,j).
Let α:K → L be a tower map.

The left maps of the canonical Milnor sequences commute with the induced lim¹ map and middle map: f_L∘lim¹(H_iα)=H_j(lim α)∘f_K. -/
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
/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape, and K,L inverse towers of complexes.
Assume their product differences Δ(x)ₙ=xₙ−tₙ(xₙ₊₁) are epic and c.Rel(i,j).
Let α:K → L be a tower map.

The right maps of the canonical Milnor sequences satisfy g_L∘H_j(lim α)=lim(H_jα)∘g_K. -/
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

/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape, and K,L inverse towers of complexes.
Assume their product differences Δ(x)ₙ=xₙ−tₙ(xₙ₊₁) are epic and c.Rel(i,j).
Let α:K → L be a tower map.

The morphism between canonical Milnor short complexes has three components lim¹(H_iα), H_j(lim α), and lim(H_jα). -/
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
/-- Let C be abelian, c an arbitrary complex shape and K a sequential
inverse tower of complexes of shape c. Assume C has exact countable products and sequential inverse limits,
Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, and c.Rel(i,j).
Write H_aK=(H_a(Kₙ))ₙ, β_a:H_a(P(K)) ≅ P(H_aK),
and lim¹(H_iK)=Coker(Δ_{H_iK}).

The morphism of canonical Milnor short complexes induced by the identity tower map is the identity of the Milnor short complex. -/
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
/-- Let C be abelian with exact countable products and sequential inverse limits, c any complex shape, and K,L,M towers whose product differences are epic. Take c.Rel(i,j) and tower maps α:K → L, β:L → M.

The Milnor-sequence morphism induced by β∘α equals the composite of the morphisms induced by α and β. -/
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
