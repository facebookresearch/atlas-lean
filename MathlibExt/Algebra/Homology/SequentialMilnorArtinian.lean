/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.Artinian
public import MathlibExt.Algebra.Homology.SequentialMilnor
public import MathlibExt.Algebra.Category.ModuleCat.MittagLefflerArtinian
public import MathlibExt.Algebra.Category.ModuleCat.SequentialMittagLeffler

/-!
# Artinian inverse systems and the actual Milnor edge

The preceding homology tower controls the kernel of the actual Milnor edge.
Vanishing of its concrete sequential `lim¹` makes that edge an isomorphism.
Artinian module homology supplies this vanishing through native Mittag--Leffler.
Degreewise Artinian terms additionally make the actual DIFFERENCE epi through
the existing module and degreewise APIs. Original transitions need not be epi.

The relation between the preceding and current degrees remains explicit.
No global limit-preserves-homology instance is introduced.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace HomologicalComplex

section Vanishing

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι}
  [HasCountableProducts C] [CountableAB4Star C]
  [HasLimitsOfShape ℕᵒᵖ C]

/-- Vanishing of the preceding concrete lim-one makes the actual Milnor edge iso. -/
theorem isIso_sequentialMilnorEdge_of_isZero
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j)
    (h₁ : IsZero (sequentialLimOne (sequentialHomologyTower K i))) :
    IsIso (sequentialMilnorEdge K hK i j hij) := by
  have hS := sequentialMilnorShortComplex_shortExact K hK i j hij
  have hX : IsZero (sequentialMilnorShortComplex K hK i j hij).X₁ := by
    rw [sequentialMilnorShortComplex_X₁]
    exact h₁
  have h := (hS.isIso_g_iff).mpr hX
  simpa only [sequentialMilnorShortComplex_g, sequentialMilnorShortComplex_X₂,
    sequentialMilnorShortComplex_X₃] using h

/-- The canonical comparison is the isomorphism of the actual Milnor edge. -/
def sequentialMilnorIsoOfIsZero
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j)
    (h₁ : IsZero (sequentialLimOne (sequentialHomologyTower K i))) :
    (limit K).homology j ≅ limit (sequentialHomologyTower K j) := by
  have : IsIso (sequentialMilnorEdge K hK i j hij) :=
    isIso_sequentialMilnorEdge_of_isZero K hK i j hij h₁
  exact asIso (sequentialMilnorEdge K hK i j hij)

/-- The forward comparison is exactly the actual Milnor edge. -/
@[simp]
theorem sequentialMilnorIsoOfIsZero_hom
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j)
    (h₁ : IsZero (sequentialLimOne (sequentialHomologyTower K i))) :
    (sequentialMilnorIsoOfIsZero K hK i j hij h₁).hom =
      sequentialMilnorEdge K hK i j hij := rfl

/-- Each forward coordinate is the actual homology map of the limit projection. -/
@[reassoc]
theorem sequentialMilnorIsoOfIsZero_hom_π
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j)
    (h₁ : IsZero (sequentialLimOne (sequentialHomologyTower K i))) (n : ℕ) :
    (sequentialMilnorIsoOfIsZero K hK i j hij h₁).hom ≫
        limit.π (sequentialHomologyTower K j) (op n) =
      homologyMap (limit.π K (op n)) j := by
  simpa only [sequentialMilnorIsoOfIsZero_hom] using
    sequentialMilnorEdge_π K hK i j hij n

/-- The inverse comparison retains the actual stage projections. -/
@[reassoc (attr := simp)]
theorem sequentialMilnorIsoOfIsZero_inv_π
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (hK : Epi (sequentialDifference K))
    (i j : ι) (hij : c.Rel i j)
    (h₁ : IsZero (sequentialLimOne (sequentialHomologyTower K i))) (n : ℕ) :
    (sequentialMilnorIsoOfIsZero K hK i j hij h₁).inv ≫
        homologyMap (limit.π K (op n)) j =
      limit.π (sequentialHomologyTower K j) (op n) := by
  exact (congrArg (fun f : (limit K).homology j ⟶ (K.obj (op n)).homology j =>
      (sequentialMilnorIsoOfIsZero K hK i j hij h₁).inv ≫ f)
    (sequentialMilnorIsoOfIsZero_hom_π K hK i j hij h₁ n).symm).trans
      (Iso.inv_hom_id_assoc (sequentialMilnorIsoOfIsZero K hK i j hij h₁)
        (limit.π (sequentialHomologyTower K j) (op n)))

/-- The comparison is natural through the actual maps on limits and homology. -/
@[reassoc]
theorem sequentialMilnorIsoOfIsZero_naturality
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (hK : Epi (sequentialDifference K)) (hL : Epi (sequentialDifference L))
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j)
    (hK₁ : IsZero (sequentialLimOne (sequentialHomologyTower K i)))
    (hL₁ : IsZero (sequentialLimOne (sequentialHomologyTower L i))) :
    homologyMap (limMap α) j ≫
        (sequentialMilnorIsoOfIsZero L hL i j hij hL₁).hom =
      (sequentialMilnorIsoOfIsZero K hK i j hij hK₁).hom ≫
        limMap (sequentialHomologyTowerMap α j) := by
  simpa only [sequentialMilnorIsoOfIsZero_hom] using
    sequentialMilnorEdge_naturality hK hL α i j hij

end Vanishing

section Modules

variable {R : Type u} [Ring R] {ι : Type v} {c : ComplexShape ι}

/-- Artinian degree-i objects give native ML of the existing degree tower. -/
theorem isMittagLeffler_sequentialDegreeTower_of_isArtinian
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c) (i : ι)
    (h : ∀ n : ℕ, IsArtinian R ((K.obj (op n)).X i)) :
    (sequentialDegreeTower K i).IsSequentialMittagLeffler := by
  apply ModuleCat.isMittagLeffler_of_isArtinian
  rintro ⟨n⟩
  exact h n

/-- Artinian homology objects give native ML of the existing homology tower. -/
theorem isMittagLeffler_sequentialHomologyTower_of_isArtinian
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c) (i : ι)
    (h : ∀ n : ℕ, IsArtinian R ((K.obj (op n)).homology i)) :
    (sequentialHomologyTower K i).IsSequentialMittagLeffler := by
  apply ModuleCat.isMittagLeffler_of_isArtinian
  rintro ⟨n⟩
  exact h n

/-- A single degree of Artinian terms supplies ML of its homology tower. -/
theorem isMittagLeffler_sequentialHomologyTower_of_isArtinian_degree
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c) (i : ι)
    (h : ∀ n : ℕ, IsArtinian R ((K.obj (op n)).X i)) :
    (sequentialHomologyTower K i).IsSequentialMittagLeffler := by
  apply isMittagLeffler_sequentialHomologyTower_of_isArtinian
  intro n
  have : IsArtinian R ((K.obj (op n)).X i) := h n
  exact (K.obj (op n)).isArtinian_homology_of_isArtinian_degree i

/-- Degreewise Artinian terms make the actual complex-level DIFFERENCE epi. -/
theorem epi_sequentialDifference_of_degreewise_isArtinian
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (h : ∀ (i : ι) (n : ℕ), IsArtinian R ((K.obj (op n)).X i)) :
    Epi (sequentialDifference K) :=
  epi_sequentialDifference_of_epi_degreewise K fun i =>
    ModuleCat.epi_sequentialDifference_of_isMittagLeffler (sequentialDegreeTower K i)
      (isMittagLeffler_sequentialDegreeTower_of_isArtinian K i (h i))

variable [CountableAB4Star (ModuleCat.{w} R)]

/-- Preceding Artinian homology suffices, keeping the explicit difference-epi gate. -/
theorem isIso_sequentialMilnorEdge_of_isArtinian_homology
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (hK : Epi (sequentialDifference K)) (i j : ι) (hij : c.Rel i j)
    (h : ∀ n : ℕ, IsArtinian R ((K.obj (op n)).homology i)) :
    IsIso (sequentialMilnorEdge K hK i j hij) :=
  isIso_sequentialMilnorEdge_of_isZero K hK i j hij
    (ModuleCat.isZero_sequentialLimOne_of_isMittagLeffler
      (sequentialHomologyTower K i)
      (isMittagLeffler_sequentialHomologyTower_of_isArtinian K i h))

/-- A single preceding degree of Artinian terms also suffices with the same gate. -/
theorem isIso_sequentialMilnorEdge_of_isArtinian_degree
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (hK : Epi (sequentialDifference K)) (i j : ι) (hij : c.Rel i j)
    (h : ∀ n : ℕ, IsArtinian R ((K.obj (op n)).X i)) :
    IsIso (sequentialMilnorEdge K hK i j hij) :=
  isIso_sequentialMilnorEdge_of_isZero K hK i j hij
    (ModuleCat.isZero_sequentialLimOne_of_isMittagLeffler
      (sequentialHomologyTower K i)
      (isMittagLeffler_sequentialHomologyTower_of_isArtinian_degree K i h))

/-- The actual edge is iso when every degree of the tower is Artinian. -/
theorem isIso_sequentialMilnorEdge_of_degreewise_isArtinian
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (h : ∀ (a : ι) (n : ℕ), IsArtinian R ((K.obj (op n)).X a))
    (i j : ι) (hij : c.Rel i j) :
    IsIso (sequentialMilnorEdge K
      (epi_sequentialDifference_of_degreewise_isArtinian K h) i j hij) :=
  isIso_sequentialMilnorEdge_of_isArtinian_degree K
    (epi_sequentialDifference_of_degreewise_isArtinian K h) i j hij (h i)

/-- The comparison for preceding Artinian homology is the actual Milnor edge iso. -/
def sequentialMilnorIsoOfIsArtinianHomology
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (hK : Epi (sequentialDifference K)) (i j : ι) (hij : c.Rel i j)
    (h : ∀ n : ℕ, IsArtinian R ((K.obj (op n)).homology i)) :
    (limit K).homology j ≅ limit (sequentialHomologyTower K j) :=
  sequentialMilnorIsoOfIsZero K hK i j hij
    (ModuleCat.isZero_sequentialLimOne_of_isMittagLeffler
      (sequentialHomologyTower K i)
      (isMittagLeffler_sequentialHomologyTower_of_isArtinian K i h))

/-- The degreewise convenience comparison keeps the actual chosen endpoints and edge. -/
def sequentialMilnorIsoOfDegreewiseIsArtinian
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (h : ∀ (a : ι) (n : ℕ), IsArtinian R ((K.obj (op n)).X a))
    (i j : ι) (hij : c.Rel i j) :
    (limit K).homology j ≅ limit (sequentialHomologyTower K j) :=
  sequentialMilnorIsoOfIsZero K
    (epi_sequentialDifference_of_degreewise_isArtinian K h) i j hij
    (ModuleCat.isZero_sequentialLimOne_of_isMittagLeffler
      (sequentialHomologyTower K i)
      (isMittagLeffler_sequentialHomologyTower_of_isArtinian_degree K i (h i)))

/-- The preceding-homology comparison has the actual edge as its forward map. -/
@[simp]
theorem sequentialMilnorIsoOfIsArtinianHomology_hom
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (hK : Epi (sequentialDifference K)) (i j : ι) (hij : c.Rel i j)
    (h : ∀ n : ℕ, IsArtinian R ((K.obj (op n)).homology i)) :
    (sequentialMilnorIsoOfIsArtinianHomology K hK i j hij h).hom =
      sequentialMilnorEdge K hK i j hij := rfl

/-- The degreewise comparison has the actual edge as its forward map. -/
@[simp]
theorem sequentialMilnorIsoOfDegreewiseIsArtinian_hom
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{w} R) c)
    (h : ∀ (a : ι) (n : ℕ), IsArtinian R ((K.obj (op n)).X a))
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorIsoOfDegreewiseIsArtinian K h i j hij).hom =
      sequentialMilnorEdge K
        (epi_sequentialDifference_of_degreewise_isArtinian K h) i j hij := rfl

end Modules

end HomologicalComplex
