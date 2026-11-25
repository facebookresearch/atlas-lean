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

public import MathlibExt.Algebra.Homology.SequentialMilnor
public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialSplitDifference

/-!
# Milnor sequences from actual degreewise split transitions

Specified sections of the actual adjacent maps earn epimorphy of the standard
product difference of complexes. The existing sequential Milnor construction
then gives the exact sequence with its original lim¹ and inverse-limit endpoints.
Its naturality needs no compatibility between choices of transition sections.
Exact countable products are needed for the homology comparison, not for the
recursive difference section.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Opposite

namespace HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι} [HasCountableProducts C]

/-- Actual sections in each degree suffice; they need not be maps of complexes. -/
abbrev SequentialDegreeSections (K : ℕᵒᵖ ⥤ HomologicalComplex C c) :=
  ∀ (i : ι) (n : ℕ), (K.obj (op n)).X i ⟶ (K.obj (op (n + 1))).X i

/-- Degreewise finite recursive solutions make the original complex difference epi. -/
theorem epi_sequentialDifference_of_degree_sections
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (i : ι) (n : ℕ),
      s i n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f i = 𝟙 _) :
    Epi (sequentialDifference K) :=
  epi_sequentialDifference_of_epi_degreewise K fun i =>
    epi_sequentialDifference_of_sections (sequentialDegreeTower K i) (s i) (hs i)

variable [CountableAB4Star C] [HasLimitsOfShape ℕᵒᵖ C]

/-- The canonical Milnor sequence, with its difference-epi gate earned from original sections. -/
def sequentialMilnorOfDegreeSections
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (a : ι) (n : ℕ),
      s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (i j : ι) (hij : c.Rel i j) : ShortComplex C :=
  sequentialMilnorShortComplex K (epi_sequentialDifference_of_degree_sections K s hs) i j hij

/-- The resulting exactness is inherited from the actual Milnor LES construction. -/
theorem sequentialMilnorOfDegreeSections_shortExact
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (a : ι) (n : ℕ),
      s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorOfDegreeSections K s hs i j hij).ShortExact :=
  sequentialMilnorShortComplex_shortExact K
    (epi_sequentialDifference_of_degree_sections K s hs) i j hij

/-- The left endpoint is concrete lim¹ of the preceding homology tower. -/
@[simp]
theorem sequentialMilnorOfDegreeSections_X₁
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (a : ι) (n : ℕ),
      s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorOfDegreeSections K s hs i j hij).X₁ =
      sequentialLimOne (sequentialHomologyTower K i) := rfl

/-- The middle is the actual homology of the original tower limit. -/
@[simp]
theorem sequentialMilnorOfDegreeSections_X₂
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (a : ι) (n : ℕ),
      s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorOfDegreeSections K s hs i j hij).X₂ = (limit K).homology j := rfl

/-- The right endpoint is the original chosen limit of the current homology tower. -/
@[simp]
theorem sequentialMilnorOfDegreeSections_X₃
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (a : ι) (n : ℕ),
      s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorOfDegreeSections K s hs i j hij).X₃ =
      limit (sequentialHomologyTower K j) := rfl

/-- The canonical edge retains each actual homology projection. -/
@[reassoc]
theorem sequentialMilnorOfDegreeSections_g_π
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (a : ι) (n : ℕ),
      s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (i j : ι) (hij : c.Rel i j) (n : ℕ) :
    (sequentialMilnorOfDegreeSections K s hs i j hij).g ≫
        limit.π (sequentialHomologyTower K j) (op n) =
      homologyMap (limit.π K (op n)) j :=
  sequentialMilnorEdge_π K (epi_sequentialDifference_of_degree_sections K s hs) i j hij n

/-- The exact sequences remain natural even when the section choices do not commute. -/
def sequentialMilnorOfDegreeSectionsMap
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (s : SequentialDegreeSections K) (t : SequentialDegreeSections L)
    (hs : ∀ (a : ι) (n : ℕ), s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (ht : ∀ (a : ι) (n : ℕ), t a n ≫ (L.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    sequentialMilnorOfDegreeSections K s hs i j hij ⟶
      sequentialMilnorOfDegreeSections L t ht i j hij :=
  sequentialMilnorShortComplexMap
    (epi_sequentialDifference_of_degree_sections K s hs)
    (epi_sequentialDifference_of_degree_sections L t ht) α i j hij

/-- The left map of sequence maps is the original induced concrete lim¹ map. -/
@[simp]
theorem sequentialMilnorOfDegreeSectionsMap_τ₁
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (s : SequentialDegreeSections K) (t : SequentialDegreeSections L)
    (hs : ∀ (a : ι) (n : ℕ), s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (ht : ∀ (a : ι) (n : ℕ), t a n ≫ (L.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorOfDegreeSectionsMap s t hs ht α i j hij).τ₁ =
      sequentialLimOneMap (sequentialHomologyTowerMap α i) := rfl

/-- The middle is homology of the actual limit map. -/
@[simp]
theorem sequentialMilnorOfDegreeSectionsMap_τ₂
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (s : SequentialDegreeSections K) (t : SequentialDegreeSections L)
    (hs : ∀ (a : ι) (n : ℕ), s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (ht : ∀ (a : ι) (n : ℕ), t a n ≫ (L.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorOfDegreeSectionsMap s t hs ht α i j hij).τ₂ =
      homologyMap (limMap α) j := rfl

/-- The right map is the actual map between limits of homology towers. -/
@[simp]
theorem sequentialMilnorOfDegreeSectionsMap_τ₃
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (s : SequentialDegreeSections K) (t : SequentialDegreeSections L)
    (hs : ∀ (a : ι) (n : ℕ), s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (ht : ∀ (a : ι) (n : ℕ), t a n ≫ (L.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorOfDegreeSectionsMap s t hs ht α i j hij).τ₃ =
      limMap (sequentialHomologyTowerMap α j) := rfl

/-- Changing no tower map gives the actual identity of the canonical Milnor sequence. -/
@[simp]
theorem sequentialMilnorOfDegreeSectionsMap_id
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (a : ι) (n : ℕ), s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (i j : ι) (hij : c.Rel i j) :
    sequentialMilnorOfDegreeSectionsMap s s hs hs (𝟙 K) i j hij =
      𝟙 (sequentialMilnorOfDegreeSections K s hs i j hij) :=
  sequentialMilnorShortComplexMap_id K
    (epi_sequentialDifference_of_degree_sections K s hs) i j hij

/-- Composition is independent of any coherence of the chosen sections. -/
@[reassoc]
theorem sequentialMilnorOfDegreeSectionsMap_comp
    {K L M : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (s : SequentialDegreeSections K) (t : SequentialDegreeSections L)
    (r : SequentialDegreeSections M)
    (hs : ∀ (a : ι) (n : ℕ), s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (ht : ∀ (a : ι) (n : ℕ), t a n ≫ (L.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (hr : ∀ (a : ι) (n : ℕ), r a n ≫ (M.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (α : K ⟶ L) (β : L ⟶ M) (i j : ι) (hij : c.Rel i j) :
    sequentialMilnorOfDegreeSectionsMap s r hs hr (α ≫ β) i j hij =
      sequentialMilnorOfDegreeSectionsMap s t hs ht α i j hij ≫
        sequentialMilnorOfDegreeSectionsMap t r ht hr β i j hij :=
  sequentialMilnorShortComplexMap_comp
    (epi_sequentialDifference_of_degree_sections K s hs)
    (epi_sequentialDifference_of_degree_sections L t ht)
    (epi_sequentialDifference_of_degree_sections M r hr) α β i j hij

end HomologicalComplex
