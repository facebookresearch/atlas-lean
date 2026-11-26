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
# Milnor sequences from degreewise split transitions

Let C be abelian with countable products and K an inverse tower of complexes
of any shape c. For each degree a and stage n, choose
sₙᵃ:Kₙᵃ → Kₙ₊₁ᵃ with tₙᵃ∘sₙᵃ=1.
The finite recursive solutions of the degreewise difference equations
make Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) epic.

If countable products are exact and sequential inverse limits exist, every
c.Rel(i,j) gives the canonical short exact Milnor sequence
0 → lim¹(H_iK) → H_j(lim K) → lim(H_jK) → 0.
Its edge retains the homology maps of stage projections. For independently
chosen degreewise sections on two towers, every tower map induces the
canonical morphism of these sequences, respecting identities and composition.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Opposite

namespace HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι} [HasCountableProducts C]

/-- For an inverse tower K of complexes of any shape in an abelian category
with countable products, the family of reverse component maps
sₙᵃ:Kₙᵃ → Kₙ₊₁ᵃ. These maps can serve as degreewise sections when
tₙᵃ∘sₙᵃ=1; the family itself consists only of maps between terms. -/
abbrev SequentialDegreeSections (K : ℕᵒᵖ ⥤ HomologicalComplex C c) :=
  ∀ (i : ι) (n : ℕ), (K.obj (op n)).X i ⟶ (K.obj (op (n + 1))).X i

/-- Let C be abelian with countable products, c any complex shape and K an
inverse tower of complexes. Let sₙᵃ:Kₙᵃ → Kₙ₊₁ᵃ satisfy
tₙᵃ∘sₙᵃ=1 for every degree a and stage n.

The product difference Δ_K(x)ₙ=xₙ−tₙ(xₙ₊₁) is epic, by finite recursive solutions of its component equations. -/
theorem epi_sequentialDifference_of_degree_sections
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (i : ι) (n : ℕ),
      s i n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f i = 𝟙 _) :
    Epi (sequentialDifference K) :=
  epi_sequentialDifference_of_epi_degreewise K fun i =>
    epi_sequentialDifference_of_sections (sequentialDegreeTower K i) (s i) (hs i)

variable [CountableAB4Star C] [HasLimitsOfShape ℕᵒᵖ C]

/-- Let C be abelian with countable products, c any complex shape and K an
inverse tower of complexes. Let sₙᵃ:Kₙᵃ → Kₙ₊₁ᵃ satisfy
tₙᵃ∘sₙᵃ=1 for every degree a and stage n. Assume countable products in C are exact, sequential inverse
limits exist, and c.Rel(i,j).

The canonical Milnor short complex lim¹(H_iK) → H_j(lim K) → lim(H_jK), with epimorphy of Δ_K supplied by the degreewise sections. -/
def sequentialMilnorOfDegreeSections
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (a : ι) (n : ℕ),
      s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (i j : ι) (hij : c.Rel i j) : ShortComplex C :=
  sequentialMilnorShortComplex K (epi_sequentialDifference_of_degree_sections K s hs) i j hij

/-- Let C be abelian with countable products, c any complex shape and K an
inverse tower of complexes. Let sₙᵃ:Kₙᵃ → Kₙ₊₁ᵃ satisfy
tₙᵃ∘sₙᵃ=1 for every degree a and stage n. Assume countable products in C are exact, sequential inverse
limits exist, and c.Rel(i,j).

The Milnor sequence supplied by the degreewise sections is short exact. -/
theorem sequentialMilnorOfDegreeSections_shortExact
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (a : ι) (n : ℕ),
      s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorOfDegreeSections K s hs i j hij).ShortExact :=
  sequentialMilnorShortComplex_shortExact K
    (epi_sequentialDifference_of_degree_sections K s hs) i j hij

/-- Let C be abelian with countable products, c any complex shape and K an
inverse tower of complexes. Let sₙᵃ:Kₙᵃ → Kₙ₊₁ᵃ satisfy
tₙᵃ∘sₙᵃ=1 for every degree a and stage n. Assume countable products in C are exact, sequential inverse
limits exist, and c.Rel(i,j).

The left term of the sequence is the concrete cokernel lim¹(H_iK)=Coker(Δ_{H_iK}). -/
@[simp]
theorem sequentialMilnorOfDegreeSections_X₁
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (a : ι) (n : ℕ),
      s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorOfDegreeSections K s hs i j hij).X₁ =
      sequentialLimOne (sequentialHomologyTower K i) := rfl

/-- Let C be abelian with countable products, c any complex shape and K an
inverse tower of complexes. Let sₙᵃ:Kₙᵃ → Kₙ₊₁ᵃ satisfy
tₙᵃ∘sₙᵃ=1 for every degree a and stage n. Assume countable products in C are exact, sequential inverse
limits exist, and c.Rel(i,j).

The middle term of the sequence is H_j(lim K). -/
@[simp]
theorem sequentialMilnorOfDegreeSections_X₂
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (a : ι) (n : ℕ),
      s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorOfDegreeSections K s hs i j hij).X₂ = (limit K).homology j := rfl

/-- Let C be abelian with countable products, c any complex shape and K an
inverse tower of complexes. Let sₙᵃ:Kₙᵃ → Kₙ₊₁ᵃ satisfy
tₙᵃ∘sₙᵃ=1 for every degree a and stage n. Assume countable products in C are exact, sequential inverse
limits exist, and c.Rel(i,j).

The right term of the sequence is lim(H_jK). -/
@[simp]
theorem sequentialMilnorOfDegreeSections_X₃
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (a : ι) (n : ℕ),
      s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorOfDegreeSections K s hs i j hij).X₃ =
      limit (sequentialHomologyTower K j) := rfl

/-- Let C be abelian with countable products, c any complex shape and K an
inverse tower of complexes. Let sₙᵃ:Kₙᵃ → Kₙ₊₁ᵃ satisfy
tₙᵃ∘sₙᵃ=1 for every degree a and stage n. Assume countable products in C are exact, sequential inverse
limits exist, and c.Rel(i,j).

For every stage n, the sequence edge followed by lim(H_jK) → H_j(Kₙ) equals H_j of lim K → Kₙ. -/
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

/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape and α:K → L a map of inverse towers.
Choose degreewise sections s for K and t for L, each a right inverse
of its adjacent transition, and assume c.Rel(i,j).

The canonical morphism of the two Milnor short complexes induced by α, using the epic differences supplied by the respective sections. -/
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

/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape and α:K → L a map of inverse towers.
Choose degreewise sections s for K and t for L, each a right inverse
of its adjacent transition, and assume c.Rel(i,j).

The first component of this sequence morphism is lim¹(H_iα), induced by the degree-i homology tower map. -/
@[simp]
theorem sequentialMilnorOfDegreeSectionsMap_τ₁
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (s : SequentialDegreeSections K) (t : SequentialDegreeSections L)
    (hs : ∀ (a : ι) (n : ℕ), s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (ht : ∀ (a : ι) (n : ℕ), t a n ≫ (L.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorOfDegreeSectionsMap s t hs ht α i j hij).τ₁ =
      sequentialLimOneMap (sequentialHomologyTowerMap α i) := rfl

/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape and α:K → L a map of inverse towers.
Choose degreewise sections s for K and t for L, each a right inverse
of its adjacent transition, and assume c.Rel(i,j).

The middle component of this sequence morphism is H_j(lim α). -/
@[simp]
theorem sequentialMilnorOfDegreeSectionsMap_τ₂
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (s : SequentialDegreeSections K) (t : SequentialDegreeSections L)
    (hs : ∀ (a : ι) (n : ℕ), s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (ht : ∀ (a : ι) (n : ℕ), t a n ≫ (L.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorOfDegreeSectionsMap s t hs ht α i j hij).τ₂ =
      homologyMap (limMap α) j := rfl

/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape and α:K → L a map of inverse towers.
Choose degreewise sections s for K and t for L, each a right inverse
of its adjacent transition, and assume c.Rel(i,j).

The right component of this sequence morphism is lim(H_jα). -/
@[simp]
theorem sequentialMilnorOfDegreeSectionsMap_τ₃
    {K L : ℕᵒᵖ ⥤ HomologicalComplex C c}
    (s : SequentialDegreeSections K) (t : SequentialDegreeSections L)
    (hs : ∀ (a : ι) (n : ℕ), s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (ht : ∀ (a : ι) (n : ℕ), t a n ≫ (L.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (α : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    (sequentialMilnorOfDegreeSectionsMap s t hs ht α i j hij).τ₃ =
      limMap (sequentialHomologyTowerMap α j) := rfl

/-- Let C be abelian with countable products, c any complex shape and K an
inverse tower of complexes. Let sₙᵃ:Kₙᵃ → Kₙ₊₁ᵃ satisfy
tₙᵃ∘sₙᵃ=1 for every degree a and stage n. Assume countable products in C are exact, sequential inverse
limits exist, and c.Rel(i,j).

The sequence morphism induced by the identity of K, with its fixed degreewise sections, is the identity of its Milnor sequence. -/
@[simp]
theorem sequentialMilnorOfDegreeSectionsMap_id
    (K : ℕᵒᵖ ⥤ HomologicalComplex C c) (s : SequentialDegreeSections K)
    (hs : ∀ (a : ι) (n : ℕ), s a n ≫ (K.map (homOfLE (Nat.le_succ n)).op).f a = 𝟙 _)
    (i j : ι) (hij : c.Rel i j) :
    sequentialMilnorOfDegreeSectionsMap s s hs hs (𝟙 K) i j hij =
      𝟙 (sequentialMilnorOfDegreeSections K s hs i j hij) :=
  sequentialMilnorShortComplexMap_id K
    (epi_sequentialDifference_of_degree_sections K s hs) i j hij

/-- Let C be abelian with exact countable products and sequential inverse
limits, c any complex shape, and K,L,M inverse towers with independently
chosen degreewise sections of every adjacent transition.
For c.Rel(i,j) and maps α:K → L, β:L → M, the Milnor sequence morphism
of β∘α equals the composite of the morphisms of α and β. -/
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
