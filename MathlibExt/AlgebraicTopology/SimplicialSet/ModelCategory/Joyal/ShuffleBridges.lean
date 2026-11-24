/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PrismVerticals
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.ShuffleCobase

/-!
# Functor-form bridges for shuffle horn filling (the supporting results)

This module attacks the additional comparison obligation of `ShuffleCobase.lean`
(lines 171–185 there), which is the additional comparison obligation of
`CobaseUnconditional.lean` unchanged, together with
the additional comparison obligation = the additional comparison obligation
(`SSet.CompCorrection ((pre i).app C)`).
The target is the unconditional instance

```text
(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet.{u}),
```
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

/-- Two simplices of `Δ[m]` whose order maps agree at every index are
equal. Local copy: the upstream lemma of this name in
`CoherentIsoEndpoint.lean` is `private` in the landed version. -/
private lemma stdSimplex_ext_asOrderHom {m : ℕ} {Δ : SimplexCategoryᵒᵖ}
    {x y : (Δ[m] : SSet.{u}).obj Δ}
    (h : ∀ k : Fin (Δ.unop.len + 1),
      (stdSimplex.asOrderHom x) k = (stdSimplex.asOrderHom y) k) :
    x = y := by
  apply stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  exact OrderHom.ext _ _ (funext fun k => h k)

/-!
## Shuffle initial subcomplexes and special edges (§1)

The initial subcomplexes `S₀ = ∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2,0]` and
`S₂ = ∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2,2]` of `Δ[n] ⊗ Δ[2]`, the
special vertical edges `v₀ = ((0,0) ⟶ (0,1))` and
`v₂ = ((n,1) ⟶ (n,2))` as componentwise pairs, and the
horn-vertical simplices over a general base through which the
functor form states its special-edge hypotheses.
-/

section ShuffleInitials

variable {n : ℕ} {B : SSet.{u}}

/-- The `(0 ⟶ 1)`-edge of `Δ[2]`. -/
noncomputable abbrev shuffleEdge01 : (Δ[2] : SSet.{u}) _⦋1⦌ :=
  stdSimplex.edge 2 0 ⟨1, by decide⟩ (Fin.zero_le _)

/-- The `(1 ⟶ 2)`-edge of `Δ[2]`. -/
noncomputable abbrev shuffleEdge12 : (Δ[2] : SSet.{u}) _⦋1⦌ :=
  stdSimplex.edge 2 ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)

/-- The horn-zero initial subcomplex of the shuffle prism:
`∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2,0]`. -/
noncomputable abbrev shuffleInit0 (n : ℕ) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex :=
  Subcomplex.unionProd ∂Δ[n] Λ[2, 0]

/-- The horn-two initial subcomplex of the shuffle prism:
`∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2,2]`. -/
noncomputable abbrev shuffleInit2 (n : ℕ) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex :=
  Subcomplex.unionProd ∂Δ[n] Λ[2, 2]

/-- The special edge of the horn-zero shuffle filtration: the
vertical edge `((0,0) ⟶ (0,1))` of `Δ[n] ⊗ Δ[2]`, as the pair
of the degenerate simplex at vertex `0` and the
`(0 ⟶ 1)`-edge of `Δ[2]`. -/
noncomputable def shuffleVert0 (n : ℕ) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋1⦌ :=
  (Δ[n].σ 0 (stdSimplex.obj₀Equiv.symm 0), shuffleEdge01)

/-- The special edge of the horn-two shuffle filtration: the
vertical edge `((n,1) ⟶ (n,2))` of `Δ[n] ⊗ Δ[2]`. -/
noncomputable def shuffleVert2 (n : ℕ) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋1⦌ :=
  (Δ[n].σ 0 (stdSimplex.obj₀Equiv.symm (Fin.last n)), shuffleEdge12)

lemma shuffleVert0_fst (n : ℕ) :
    (shuffleVert0 n).1 =
      Δ[n].σ 0 (stdSimplex.obj₀Equiv.symm 0) :=
  rfl

lemma shuffleVert0_snd (n : ℕ) :
    (shuffleVert0 n).2 = shuffleEdge01 :=
  rfl

lemma shuffleVert2_fst (n : ℕ) :
    (shuffleVert2 n).1 =
      Δ[n].σ 0 (stdSimplex.obj₀Equiv.symm (Fin.last n)) :=
  rfl

lemma shuffleVert2_snd (n : ℕ) :
    (shuffleVert2 n).2 = shuffleEdge12 :=
  rfl

/-- The `(0 ⟶ 1)`-edge of `Δ[2]` lies in `Λ[2,0]`: its range
misses the vertex `2`. -/
lemma shuffleEdge01_mem_hornZero :
    shuffleEdge01 ∈ Λ[2, (0 : Fin 3)].obj _ := by
  rw [mem_horn_iff_notMem_range]
  refine ⟨⟨2, by decide⟩, by decide, ?_⟩
  rintro ⟨t, ht⟩
  fin_cases t <;> exact absurd (congrArg Fin.val ht) (by decide)

/-- The `(1 ⟶ 2)`-edge of `Δ[2]` lies in `Λ[2,2]`: its range
misses the vertex `0`. -/
lemma shuffleEdge12_mem_hornTwo :
    shuffleEdge12 ∈ Λ[2, (2 : Fin 3)].obj _ := by
  rw [mem_horn_iff_notMem_range]
  refine ⟨0, by decide, ?_⟩
  rintro ⟨t, ht⟩
  fin_cases t <;> exact absurd (congrArg Fin.val ht) (by decide)

/-- The special edge `v₀` lies in the horn-zero initial
subcomplex for every `n`, through the horn factor. -/
lemma shuffleVert0_mem_shuffleInit0 (n : ℕ) :
    shuffleVert0 n ∈ (shuffleInit0 n).obj _ :=
  (Subcomplex.mem_unionProd_iff _ _ _).2
    (Or.inl (by rw [shuffleVert0_snd]; exact shuffleEdge01_mem_hornZero))

/-- The special edge `v₂` lies in the horn-two initial
subcomplex for every `n`, through the horn factor. -/
lemma shuffleVert2_mem_shuffleInit2 (n : ℕ) :
    shuffleVert2 n ∈ (shuffleInit2 n).obj _ :=
  (Subcomplex.mem_unionProd_iff _ _ _).2
    (Or.inl (by rw [shuffleVert2_snd]; exact shuffleEdge12_mem_hornTwo))

/-- The `(0 ⟶ 1)`-vertical simplex of `B ⊗ Λ[2,0]` at a vertex
`x` of `B`: the pair of the degenerate simplex at `x` and the
`(0 ⟶ 1)`-edge of the horn. -/
noncomputable def hornVertZeroSimplex (x : B _⦋0⦌) :
    (B ⊗ (Λ[2, 0] : SSet.{u})) _⦋1⦌ :=
  (B.σ 0 x,
    horn.edge 2 0 0 ⟨1, by decide⟩ (Fin.zero_le _) (by decide))

/-- The `(1 ⟶ 2)`-vertical simplex of `B ⊗ Λ[2,2]` at a vertex
`x` of `B`. -/
noncomputable def hornVertTwoSimplex (x : B _⦋0⦌) :
    (B ⊗ (Λ[2, 2] : SSet.{u})) _⦋1⦌ :=
  (B.σ 0 x,
    horn.edge 2 2 ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
      (by decide))

lemma hornVertZeroSimplex_fst (x : B _⦋0⦌) :
    (hornVertZeroSimplex x).1 = B.σ 0 x :=
  rfl

lemma hornVertZeroSimplex_snd_val (x : B _⦋0⦌) :
    (hornVertZeroSimplex x).2.val = shuffleEdge01 :=
  rfl

lemma hornVertTwoSimplex_fst (x : B _⦋0⦌) :
    (hornVertTwoSimplex x).1 = B.σ 0 x :=
  rfl

lemma hornVertTwoSimplex_snd_val (x : B _⦋0⦌) :
    (hornVertTwoSimplex x).2.val = shuffleEdge12 :=
  rfl

end ShuffleInitials

/-!
## The `Δ[2]` extension properties and the cell bridge (§1)

The subcomplex-form cell inputs (exact statements of the the supporting result
header), the horn-prism functor forms along a general map, and
the bridge between them over `∂Δ[n].ι` by gluing along
`Subcomplex.unionProd.isPushout`.
-/

section ShuffleCellBridge

variable {n : ℕ} {A B C : SSet.{u}} {i : A ⟶ B}

/-- **Horn-zero shuffle extension over a cell, subcomplex form**
(the the supporting result input `exists_extension_of_unionProd_boundary_horn_zero`
as a proposition): a map out of
`∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2,0]` into a quasicategory extends to
`Δ[n] ⊗ Δ[2]` as soon as the image of the vertical edge
`shuffleVert0` is an equivalence. -/
-- The quasicategory instance is part of this public statement (compatibility contract).
@[nolint unusedArguments]
def ShuffleHornZeroCellExtension (n : ℕ) (C : SSet.{u})
    [Quasicategory C] : Prop :=
  ∀ (φ₀ : ((shuffleInit0 n :
      (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C),
    (Edge.mk' (φ₀.app _ ⟨shuffleVert0 n,
        shuffleVert0_mem_shuffleInit0 n⟩)).IsEquivalence →
      ∃ P : (Δ[n] ⊗ Δ[2] : SSet.{u}) ⟶ C,
        (shuffleInit0 n).ι ≫ P = φ₀

/-- **Horn-two shuffle extension over a cell, subcomplex form**
(the mirror the supporting result input). -/
-- The quasicategory instance is part of this public statement (compatibility contract).
@[nolint unusedArguments]
def ShuffleHornTwoCellExtension (n : ℕ) (C : SSet.{u})
    [Quasicategory C] : Prop :=
  ∀ (φ₀ : ((shuffleInit2 n :
      (Δ[n] ⊗ Δ[2] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C),
    (Edge.mk' (φ₀.app _ ⟨shuffleVert2 n,
        shuffleVert2_mem_shuffleInit2 n⟩)).IsEquivalence →
      ∃ P : (Δ[n] ⊗ Δ[2] : SSet.{u}) ⟶ C,
        (shuffleInit2 n).ι ≫ P = φ₀

/-- **Horn-zero `Δ[2]`-prism extension along `i`, functor form:**
a `Δ[2]`-prism over `A` and a `Λ[2,0]`-prism over `B` agreeing
over `A ⊗ Λ[2,0]`, with every `(0 ⟶ 1)`-vertical of the horn
prism an equivalence, extend to a `Δ[2]`-prism over `B`. -/
def PrismTwoHornZeroExtension (i : A ⟶ B) (C : SSet.{u}) : Prop :=
  ∀ (P_A : A ⊗ Δ[2] ⟶ C) (P_Λ : B ⊗ (Λ[2, 0] : SSet.{u}) ⟶ C),
    (A ◁ Λ[2, 0].ι) ≫ P_A = (i ▷ (Λ[2, 0] : SSet.{u})) ≫ P_Λ →
    (∀ x : B _⦋0⦌,
      (Edge.mk' (P_Λ.app _ (hornVertZeroSimplex x))).IsEquivalence) →
      ∃ P : B ⊗ Δ[2] ⟶ C,
        (i ▷ Δ[2]) ≫ P = P_A ∧ (B ◁ Λ[2, 0].ι) ≫ P = P_Λ

/-- **Horn-two `Δ[2]`-prism extension along `i`, functor form**
(the mirror, with `(1 ⟶ 2)`-verticals). -/
def PrismTwoHornTwoExtension (i : A ⟶ B) (C : SSet.{u}) : Prop :=
  ∀ (P_A : A ⊗ Δ[2] ⟶ C) (P_Λ : B ⊗ (Λ[2, 2] : SSet.{u}) ⟶ C),
    (A ◁ Λ[2, 2].ι) ≫ P_A = (i ▷ (Λ[2, 2] : SSet.{u})) ≫ P_Λ →
    (∀ x : B _⦋0⦌,
      (Edge.mk' (P_Λ.app _ (hornVertTwoSimplex x))).IsEquivalence) →
      ∃ P : B ⊗ Δ[2] ⟶ C,
        (i ▷ Δ[2]) ≫ P = P_A ∧ (B ◁ Λ[2, 2].ι) ≫ P = P_Λ

/-- The horn factor inclusion sends the horn-vertical simplex
at vertex `0` to the special edge `shuffleVert0`. -/
lemma unionProd_ι₁_app_hornVertZeroSimplex_zero (n : ℕ) :
    (Subcomplex.unionProd.ι₁ ∂Δ[n] Λ[2, 0]).app _
        (hornVertZeroSimplex (stdSimplex.obj₀Equiv.symm 0)) =
      ⟨shuffleVert0 n, shuffleVert0_mem_shuffleInit0 n⟩ :=
  Subtype.ext rfl

/-- The horn factor inclusion sends the horn-vertical simplex
at the last vertex to the special edge `shuffleVert2`. -/
lemma unionProd_ι₁_app_hornVertTwoSimplex_last (n : ℕ) :
    (Subcomplex.unionProd.ι₁ ∂Δ[n] Λ[2, 2]).app _
        (hornVertTwoSimplex
          (stdSimplex.obj₀Equiv.symm (Fin.last n))) =
      ⟨shuffleVert2 n, shuffleVert2_mem_shuffleInit2 n⟩ :=
  Subtype.ext rfl

/-- **Functor bridge for `Δ[2]`-shuffles, horn zero, over a
cell.** Subcomplex-form shuffle filling
(`ShuffleHornZeroCellExtension`) implies horn-prism extension
along the boundary inclusion `∂Δ[n].ι`: glue the two prisms
along `Subcomplex.unionProd.isPushout`, read the special edge
through the horn factor `ι₁` as the horn-vertical at vertex
`0`, extend by the cell input, and restrict back through
`ι₁_ι`/`ι₂_ι`. This is the first step of the additional comparison obligation. -/
theorem prismTwoHornZeroExtension_boundary_of_shuffleCell
    [Quasicategory C]
    (hcell : ShuffleHornZeroCellExtension n C) :
    PrismTwoHornZeroExtension ∂Δ[n].ι C := by
  intro P_A P_Λ hagree hVert
  set sq := Subcomplex.unionProd.isPushout ∂Δ[n] Λ[2, 0] with hsq
  set φ₀ := sq.desc P_Λ P_A hagree.symm with hφ₀
  have hι₁ : Subcomplex.unionProd.ι₁ ∂Δ[n] Λ[2, 0] ≫ φ₀ = P_Λ :=
    sq.inl_desc P_Λ P_A hagree.symm
  have hι₂ : Subcomplex.unionProd.ι₂ ∂Δ[n] Λ[2, 0] ≫ φ₀ = P_A :=
    sq.inr_desc P_Λ P_A hagree.symm
  have hspec : (Edge.mk' (φ₀.app _ ⟨shuffleVert0 n,
      shuffleVert0_mem_shuffleInit0 n⟩)).IsEquivalence := by
    refine (Edge.isEquivalence_iff_of_edge_eq (e :=
        Edge.mk' (φ₀.app _ ⟨shuffleVert0 n,
          shuffleVert0_mem_shuffleInit0 n⟩)) (e' :=
        Edge.mk' (P_Λ.app _
          (hornVertZeroSimplex
            (stdSimplex.obj₀Equiv.symm 0)))) ?_).2
      (hVert (stdSimplex.obj₀Equiv.symm 0))
    change φ₀.app _ ⟨shuffleVert0 n,
        shuffleVert0_mem_shuffleInit0 n⟩ =
      P_Λ.app _ (hornVertZeroSimplex (stdSimplex.obj₀Equiv.symm 0))
    rw [← unionProd_ι₁_app_hornVertZeroSimplex_zero]
    exact congr($(hι₁).app _
      (hornVertZeroSimplex (stdSimplex.obj₀Equiv.symm 0)))
  obtain ⟨P, hP⟩ := hcell φ₀ hspec
  refine ⟨P, ?_, ?_⟩
  · have e₂ : (∂Δ[n].ι ▷ Δ[2]) =
        Subcomplex.unionProd.ι₂ ∂Δ[n] Λ[2, 0] ≫ (shuffleInit0 n).ι :=
      (Subcomplex.unionProd.ι₂_ι ∂Δ[n] Λ[2, 0]).symm
    rw [e₂, Category.assoc, hP, hι₂]
  · have e₁ : (Δ[n] ◁ Λ[2, 0].ι) =
        Subcomplex.unionProd.ι₁ ∂Δ[n] Λ[2, 0] ≫ (shuffleInit0 n).ι :=
      (Subcomplex.unionProd.ι₁_ι ∂Δ[n] Λ[2, 0]).symm
    rw [e₁, Category.assoc, hP, hι₁]

/-- **Functor bridge for `Δ[2]`-shuffles, horn two, over a
cell** (the mirror of
`prismTwoHornZeroExtension_boundary_of_shuffleCell`). -/
theorem prismTwoHornTwoExtension_boundary_of_shuffleCell
    [Quasicategory C]
    (hcell : ShuffleHornTwoCellExtension n C) :
    PrismTwoHornTwoExtension ∂Δ[n].ι C := by
  intro P_A P_Λ hagree hVert
  set sq := Subcomplex.unionProd.isPushout ∂Δ[n] Λ[2, 2] with hsq
  set φ₀ := sq.desc P_Λ P_A hagree.symm with hφ₀
  have hι₁ : Subcomplex.unionProd.ι₁ ∂Δ[n] Λ[2, 2] ≫ φ₀ = P_Λ :=
    sq.inl_desc P_Λ P_A hagree.symm
  have hι₂ : Subcomplex.unionProd.ι₂ ∂Δ[n] Λ[2, 2] ≫ φ₀ = P_A :=
    sq.inr_desc P_Λ P_A hagree.symm
  have hspec : (Edge.mk' (φ₀.app _ ⟨shuffleVert2 n,
      shuffleVert2_mem_shuffleInit2 n⟩)).IsEquivalence := by
    refine (Edge.isEquivalence_iff_of_edge_eq (e :=
        Edge.mk' (φ₀.app _ ⟨shuffleVert2 n,
          shuffleVert2_mem_shuffleInit2 n⟩)) (e' :=
        Edge.mk' (P_Λ.app _
          (hornVertTwoSimplex
            (stdSimplex.obj₀Equiv.symm (Fin.last n))))) ?_).2
      (hVert (stdSimplex.obj₀Equiv.symm (Fin.last n)))
    change φ₀.app _ ⟨shuffleVert2 n,
        shuffleVert2_mem_shuffleInit2 n⟩ =
      P_Λ.app _ (hornVertTwoSimplex
        (stdSimplex.obj₀Equiv.symm (Fin.last n)))
    rw [← unionProd_ι₁_app_hornVertTwoSimplex_last]
    exact congr($(hι₁).app _
      (hornVertTwoSimplex (stdSimplex.obj₀Equiv.symm (Fin.last n))))
  obtain ⟨P, hP⟩ := hcell φ₀ hspec
  refine ⟨P, ?_, ?_⟩
  · have e₂ : (∂Δ[n].ι ▷ Δ[2]) =
        Subcomplex.unionProd.ι₂ ∂Δ[n] Λ[2, 2] ≫ (shuffleInit2 n).ι :=
      (Subcomplex.unionProd.ι₂_ι ∂Δ[n] Λ[2, 2]).symm
    rw [e₂, Category.assoc, hP, hι₂]
  · have e₁ : (Δ[n] ◁ Λ[2, 2].ι) =
        Subcomplex.unionProd.ι₁ ∂Δ[n] Λ[2, 2] ≫ (shuffleInit2 n).ι :=
      (Subcomplex.unionProd.ι₁_ι ∂Δ[n] Λ[2, 2]).symm
    rw [e₁, Category.assoc, hP, hι₁]

end ShuffleCellBridge

/-!
## Verticals of `Δ[1]`-prisms (§2)

The neutral vertical, restriction, degenerate-prism, and section-naturality
API is imported from `PrismVerticals`.
-/

/-!
## The `Δ[1]`-prism extension properties (§2–§3)

Source- and target-prescribed prism extension along a general
map, in functor (prism) form, and closure under composition.
The cell cases and the remaining skeletal closures follow in
later sections.
-/

section PrismOneExtension

variable {A B C D : SSet.{u}} {i : A ⟶ B} {j : B ⟶ D}

/-- **Source-prescribed `Δ[1]`-prism extension along `i`:**
a prism over `A` whose source section is the restriction of
`g : B ⟶ C` and whose verticals are equivalences extends to a
prism over `B` with source section `g` and equivalence
verticals. -/
def PrismSrcExtension (i : A ⟶ B) (C : SSet.{u}) : Prop :=
  ∀ (H : A ⊗ Δ[1] ⟶ C) (g : B ⟶ C),
    prismSectionAt A 0 ≫ H = i ≫ g →
    PrismOneVerticalsEquivalences H →
      ∃ F : B ⊗ Δ[1] ⟶ C,
        (i ▷ Δ[1]) ≫ F = H ∧ prismSectionAt B 0 ≫ F = g ∧
          PrismOneVerticalsEquivalences F

/-- **Target-prescribed `Δ[1]`-prism extension along `i`**
(the mirror, with sections at vertex `1`). -/
def PrismTgtExtension (i : A ⟶ B) (C : SSet.{u}) : Prop :=
  ∀ (H : A ⊗ Δ[1] ⟶ C) (g : B ⟶ C),
    prismSectionAt A 1 ≫ H = i ≫ g →
    PrismOneVerticalsEquivalences H →
      ∃ F : B ⊗ Δ[1] ⟶ C,
        (i ▷ Δ[1]) ≫ F = H ∧ prismSectionAt B 1 ≫ F = g ∧
          PrismOneVerticalsEquivalences F

/-- Source-prescribed prism extension is stable under
composition: extend in two steps. -/
theorem PrismSrcExtension.comp (hi : PrismSrcExtension i C)
    (hj : PrismSrcExtension j C) :
    PrismSrcExtension (i ≫ j) C := by
  intro H g hagree hVert
  obtain ⟨F₁, hF₁r, hF₁s, hF₁v⟩ := hi H (j ≫ g)
    (by rw [hagree, Category.assoc]) hVert
  obtain ⟨F₂, hF₂r, hF₂s, hF₂v⟩ := hj F₁ g hF₁s hF₁v
  refine ⟨F₂, ?_, hF₂s, hF₂v⟩
  calc ((i ≫ j) ▷ Δ[1]) ≫ F₂
      = (i ▷ Δ[1]) ≫ ((j ▷ Δ[1]) ≫ F₂) := by
        rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = H := by rw [hF₂r, hF₁r]

/-- Target-prescribed prism extension is stable under
composition (the mirror). -/
theorem PrismTgtExtension.comp (hi : PrismTgtExtension i C)
    (hj : PrismTgtExtension j C) :
    PrismTgtExtension (i ≫ j) C := by
  intro H g hagree hVert
  obtain ⟨F₁, hF₁r, hF₁s, hF₁v⟩ := hi H (j ≫ g)
    (by rw [hagree, Category.assoc]) hVert
  obtain ⟨F₂, hF₂r, hF₂s, hF₂v⟩ := hj F₁ g hF₁s hF₁v
  refine ⟨F₂, ?_, hF₂s, hF₂v⟩
  calc ((i ≫ j) ▷ Δ[1]) ≫ F₂
      = (i ▷ Δ[1]) ≫ ((j ▷ Δ[1]) ≫ F₂) := by
        rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = H := by rw [hF₂r, hF₁r]

end PrismOneExtension

/-!
## Cell preliminaries for the `Δ[1]` bridges (§2)

Componentwise identification of the supporting result vertical simplices with
`verticalOneSimplex`, the face/section computation
`A ◁ (face {κ}).ι = fst ≫ prismSectionAt A κ`, boundary
membership of vertices and their degeneracies, and the direct
degenerate `n = 0` functor cases.
-/

section PrismOneCellPrelims

variable {n : ℕ} {A C W : SSet.{u}}

/-- the supporting result vertical edge at vertex `0` is the componentwise
vertical simplex at vertex `0`: both components have the same
values (`0` constantly in the first factor, the identity in
the second), checked position by position. -/
lemma prismVertZero_eq_verticalOneSimplex (n : ℕ) :
    prismVertZero n =
      verticalOneSimplex (stdSimplex.obj₀Equiv.symm 0) := by
  apply Prod.ext
  · apply stdSimplex_ext_asOrderHom
    intro t
    fin_cases t <;> rfl
  · apply stdSimplex_ext_asOrderHom
    intro t
    fin_cases t <;> rfl

/-- the supporting result vertical edge at the last vertex is the
componentwise vertical simplex there. -/
lemma prismVertLast_eq_verticalOneSimplex (n : ℕ) :
    prismVertLast n =
      verticalOneSimplex
        (stdSimplex.obj₀Equiv.symm (Fin.last n)) := by
  apply Prod.ext
  · apply stdSimplex_ext_asOrderHom
    intro t
    fin_cases t <;> rfl
  · apply stdSimplex_ext_asOrderHom
    intro t
    fin_cases t <;> rfl

/-- **Source-prescribed prism extension along `∂Δ[0].ι`,
directly by the degenerate prism.** No quasicategory
hypothesis is needed: restriction holds by uniqueness of maps
out of `(∂Δ[0] : SSet) ⊗ Δ[1]`, the source section is the
retraction `prismSectionAt_comp_fst`, and verticals are
degenerate (`prismOneVerticalsEquivalences_fst_comp`). -/
theorem prismSrcExtension_boundary_zero (C : SSet.{u}) :
    PrismSrcExtension ∂Δ[0].ι C := by
  intro H g _ _
  refine ⟨CartesianMonoidalCategory.fst _ _ ≫ g,
    eq_of_boundaryZero_tensor _ _, ?_,
    prismOneVerticalsEquivalences_fst_comp g⟩
  rw [← Category.assoc, prismSectionAt_comp_fst, Category.id_comp]

/-- **Target-prescribed prism extension along `∂Δ[0].ι`**
(the mirror, same degenerate prism). -/
theorem prismTgtExtension_boundary_zero (C : SSet.{u}) :
    PrismTgtExtension ∂Δ[0].ι C := by
  intro H g _ _
  refine ⟨CartesianMonoidalCategory.fst _ _ ≫ g,
    eq_of_boundaryZero_tensor _ _, ?_,
    prismOneVerticalsEquivalences_fst_comp g⟩
  rw [← Category.assoc, prismSectionAt_comp_fst, Category.id_comp]

end PrismOneCellPrelims

/-!
## The `Δ[1]` cell bridges (§2)

the supporting result subcomplex-form prism extensions over a cell, read in
functor form: glue `(H, g)` along `unionProd.isPushout` (the
agreement by `whiskerLeft_faceZero_ι`/`faceOne`), read the
special edge through the boundary factor as a vertical of
`H`, extend, and read back restriction, prescribed section
(pointwise through the face factor), and verticals (every
vertex lies in the boundary for `n ≥ 1`).
-/

section PrismOneCellBridge

variable {n : ℕ} {C : SSet.{u}}

/-- **Source-prescribed `Δ[1]`-prism extension along
`∂Δ[n].ι`, functor form**, from the supporting result
`exists_extension_of_unionProd_boundary_face_zero`. -/
theorem prismSrcExtension_boundary [Quasicategory C] :
    PrismSrcExtension ∂Δ[n].ι C := by
  intro H g hagree hVert
  by_cases hn0 : n = 0
  · subst hn0
    exact prismSrcExtension_boundary_zero C H g hagree hVert
  have hn : 1 ≤ n := by omega
  set gface : Δ[n] ⊗
        ((stdSimplex.face {0} :
          (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C :=
    CartesianMonoidalCategory.fst _ _ ≫ g with hgface
  have hw : (∂Δ[n].ι ▷
        ((stdSimplex.face {0} :
          (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫ gface =
      ((∂Δ[n] : SSet.{u}) ◁ (stdSimplex.face {0}).ι) ≫ H := by
    calc (∂Δ[n].ι ▷
          ((stdSimplex.face {0} :
            (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫ gface
        = (CartesianMonoidalCategory.fst (∂Δ[n] : SSet.{u}) _ ≫
            ∂Δ[n].ι) ≫ g := by
          rw [hgface, ← Category.assoc]
          congr 1
      _ = CartesianMonoidalCategory.fst (∂Δ[n] : SSet.{u}) _ ≫
            (prismSectionAt (∂Δ[n] : SSet.{u}) 0 ≫ H) := by
          rw [Category.assoc, ← hagree]
      _ = ((∂Δ[n] : SSet.{u}) ◁ (stdSimplex.face {0}).ι) ≫ H := by
          rw [whiskerLeft_faceZero_ι, Category.assoc]
  set sq := Subcomplex.unionProd.isPushout ∂Δ[n]
    (stdSimplex.face {0}) with hsq
  set φ₀ := sq.desc gface H hw with hφ₀
  have hι₁ : Subcomplex.unionProd.ι₁ ∂Δ[n]
        (stdSimplex.face {0}) ≫ φ₀ = gface :=
    sq.inl_desc gface H hw
  have hι₂ : Subcomplex.unionProd.ι₂ ∂Δ[n]
        (stdSimplex.face {0}) ≫ φ₀ = H :=
    sq.inr_desc gface H hw
  set x0b : ((∂Δ[n] : SSet.{u})) _⦋0⦌ :=
    ⟨stdSimplex.obj₀Equiv.symm 0,
      vertex_mem_boundary_of_one_le hn _⟩ with hx0b
  have happ2 : (Subcomplex.unionProd.ι₂ ∂Δ[n]
        (stdSimplex.face {0})).app _
        (verticalOneSimplex x0b) =
      ⟨prismVertZero n, prismVertZero_mem_prismSrcInitial hn⟩ := by
    apply Subtype.ext
    change (∂Δ[n].ι ▷ Δ[1]).app _ (verticalOneSimplex x0b) =
      prismVertZero n
    have happx : (∂Δ[n].ι).app _ x0b =
        stdSimplex.obj₀Equiv.symm 0 := rfl
    rw [whiskerRight_app_verticalOneSimplex,
      prismVertZero_eq_verticalOneSimplex, happx]
  have hspec : ∀ hn' : 1 ≤ n,
      (Edge.mk' (φ₀.app _ ⟨prismVertZero n,
          prismVertZero_mem_prismSrcInitial hn'⟩)).IsEquivalence := by
    intro hn'
    refine (Edge.isEquivalence_iff_of_edge_eq ?_).2 (hVert x0b)
    change φ₀.app _ ⟨prismVertZero n,
        prismVertZero_mem_prismSrcInitial hn'⟩ =
      H.app _ (verticalOneSimplex x0b)
    have helem : (⟨prismVertZero n,
          prismVertZero_mem_prismSrcInitial hn'⟩ :
          ((prismSrcInitial n :
            (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) _⦋1⦌) =
        ⟨prismVertZero n, prismVertZero_mem_prismSrcInitial hn⟩ :=
      Subtype.ext rfl
    rw [helem, ← happ2]
    exact congr($(hι₂).app _ (verticalOneSimplex x0b))
  obtain ⟨F, hF⟩ :=
    exists_extension_of_unionProd_boundary_face_zero φ₀ hspec
  refine ⟨F, ?_, ?_, ?_⟩
  · have e₂ : (∂Δ[n].ι ▷ Δ[1]) =
        Subcomplex.unionProd.ι₂ ∂Δ[n] (stdSimplex.face {0}) ≫
          (prismSrcInitial n).ι :=
      (Subcomplex.unionProd.ι₂_ι ∂Δ[n]
        (stdSimplex.face {0})).symm
    rw [e₂, Category.assoc, hF, hι₂]
  · apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro s
    have hmemFace : ((prismSectionAt (Δ[n] : SSet.{u})
          (0 : Fin 2)).app
          U s).2 ∈ (stdSimplex.face {0}).obj U := by
      change Finset.image
          (stdSimplex.objEquiv
            (((prismSectionAt (Δ[n] : SSet.{u}) (0 : Fin 2)).app
              U s).2)).toOrderHom
            ⊤ ≤ ({0} : Finset (Fin 2))
      rw [Finset.image_subset_iff]
      intro k _
      exact Finset.mem_singleton.2
        (asOrderHom_prismSectionAt_app_snd (Δ[n] : SSet.{u})
          (0 : Fin 2) s k)
    have hmem : (prismSectionAt (Δ[n] : SSet.{u}) 0).app U s ∈
        (prismSrcInitial n).obj U :=
      (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl hmemFace)
    set sface : (Δ[n] ⊗
          ((stdSimplex.face {0} :
            (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})).obj U :=
      (s, ⟨((prismSectionAt (Δ[n] : SSet.{u}) 0).app U s).2,
        hmemFace⟩) with hsface
    have happ1 : (Subcomplex.unionProd.ι₁ ∂Δ[n]
          (stdSimplex.face {0})).app U sface =
        ⟨(prismSectionAt (Δ[n] : SSet.{u}) 0).app U s, hmem⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · exact (prismSectionAt_app_fst _ _ s).symm
      · rfl
    change F.app U ((prismSectionAt (Δ[n] : SSet.{u}) 0).app U s) =
      g.app U s
    have step1 : F.app U
          ((prismSectionAt (Δ[n] : SSet.{u}) 0).app U s) =
        φ₀.app U
          ⟨(prismSectionAt (Δ[n] : SSet.{u}) 0).app U s, hmem⟩ :=
      congr($(hF).app U
        ⟨(prismSectionAt (Δ[n] : SSet.{u}) 0).app U s, hmem⟩)
    have step2 : φ₀.app U
          ⟨(prismSectionAt (Δ[n] : SSet.{u}) 0).app U s, hmem⟩ =
        gface.app U sface := by
      rw [← happ1]
      exact congr($(hι₁).app U sface)
    have step3 : gface.app U sface = g.app U s := rfl
    rw [step1, step2, step3]
  · intro x
    set xb : ((∂Δ[n] : SSet.{u})) _⦋0⦌ :=
      ⟨x, vertex_mem_boundary_of_one_le hn x⟩ with hxb
    have hmemV : verticalOneSimplex x ∈
        (prismSrcInitial n).obj _ :=
      (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inr (by
        rw [verticalOneSimplex_fst]
        exact sigma_zero_mem_boundary_of_one_le hn x))
    have happ2' : (Subcomplex.unionProd.ι₂ ∂Δ[n]
          (stdSimplex.face {0})).app _
          (verticalOneSimplex xb) =
        ⟨verticalOneSimplex x, hmemV⟩ := by
      apply Subtype.ext
      change (∂Δ[n].ι ▷ Δ[1]).app _ (verticalOneSimplex xb) =
        verticalOneSimplex x
      have happx : (∂Δ[n].ι).app _ xb = x := rfl
      rw [whiskerRight_app_verticalOneSimplex, happx]
    refine (Edge.isEquivalence_iff_of_edge_eq ?_).2 (hVert xb)
    change F.app _ (verticalOneSimplex x) =
      H.app _ (verticalOneSimplex xb)
    calc F.app _ (verticalOneSimplex x)
        = φ₀.app _ ⟨verticalOneSimplex x, hmemV⟩ :=
          congr($(hF).app _ ⟨verticalOneSimplex x, hmemV⟩)
      _ = H.app _ (verticalOneSimplex xb) := by
          rw [← happ2']
          exact congr($(hι₂).app _ (verticalOneSimplex xb))

/-- **Target-prescribed `Δ[1]`-prism extension along
`∂Δ[n].ι`, functor form** (the mirror, from the supporting result
`exists_extension_of_unionProd_boundary_face_one`). -/
theorem prismTgtExtension_boundary [Quasicategory C] :
    PrismTgtExtension ∂Δ[n].ι C := by
  intro H g hagree hVert
  by_cases hn0 : n = 0
  · subst hn0
    exact prismTgtExtension_boundary_zero C H g hagree hVert
  have hn : 1 ≤ n := by omega
  set gface : Δ[n] ⊗
        ((stdSimplex.face {1} :
          (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ C :=
    CartesianMonoidalCategory.fst _ _ ≫ g with hgface
  have hw : (∂Δ[n].ι ▷
        ((stdSimplex.face {1} :
          (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫ gface =
      ((∂Δ[n] : SSet.{u}) ◁ (stdSimplex.face {1}).ι) ≫ H := by
    calc (∂Δ[n].ι ▷
          ((stdSimplex.face {1} :
            (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})) ≫ gface
        = (CartesianMonoidalCategory.fst (∂Δ[n] : SSet.{u}) _ ≫
            ∂Δ[n].ι) ≫ g := by
          rw [hgface, ← Category.assoc]
          congr 1
      _ = CartesianMonoidalCategory.fst (∂Δ[n] : SSet.{u}) _ ≫
            (prismSectionAt (∂Δ[n] : SSet.{u}) 1 ≫ H) := by
          rw [Category.assoc, ← hagree]
      _ = ((∂Δ[n] : SSet.{u}) ◁ (stdSimplex.face {1}).ι) ≫ H := by
          rw [whiskerLeft_faceOne_ι, Category.assoc]
  set sq := Subcomplex.unionProd.isPushout ∂Δ[n]
    (stdSimplex.face {1}) with hsq
  set φ₀ := sq.desc gface H hw with hφ₀
  have hι₁ : Subcomplex.unionProd.ι₁ ∂Δ[n]
        (stdSimplex.face {1}) ≫ φ₀ = gface :=
    sq.inl_desc gface H hw
  have hι₂ : Subcomplex.unionProd.ι₂ ∂Δ[n]
        (stdSimplex.face {1}) ≫ φ₀ = H :=
    sq.inr_desc gface H hw
  set xnb : ((∂Δ[n] : SSet.{u})) _⦋0⦌ :=
    ⟨stdSimplex.obj₀Equiv.symm (Fin.last n),
      vertex_mem_boundary_of_one_le hn _⟩ with hxnb
  have happ2 : (Subcomplex.unionProd.ι₂ ∂Δ[n]
        (stdSimplex.face {1})).app _
        (verticalOneSimplex xnb) =
      ⟨prismVertLast n, prismVertLast_mem_prismTgtInitial hn⟩ := by
    apply Subtype.ext
    change (∂Δ[n].ι ▷ Δ[1]).app _ (verticalOneSimplex xnb) =
      prismVertLast n
    have happx : (∂Δ[n].ι).app _ xnb =
        stdSimplex.obj₀Equiv.symm (Fin.last n) := rfl
    rw [whiskerRight_app_verticalOneSimplex,
      prismVertLast_eq_verticalOneSimplex, happx]
  have hspec : ∀ hn' : 1 ≤ n,
      (Edge.mk' (φ₀.app _ ⟨prismVertLast n,
          prismVertLast_mem_prismTgtInitial hn'⟩)).IsEquivalence := by
    intro hn'
    refine (Edge.isEquivalence_iff_of_edge_eq ?_).2 (hVert xnb)
    change φ₀.app _ ⟨prismVertLast n,
        prismVertLast_mem_prismTgtInitial hn'⟩ =
      H.app _ (verticalOneSimplex xnb)
    have helem : (⟨prismVertLast n,
          prismVertLast_mem_prismTgtInitial hn'⟩ :
          ((prismTgtInitial n :
            (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) _⦋1⦌) =
        ⟨prismVertLast n, prismVertLast_mem_prismTgtInitial hn⟩ :=
      Subtype.ext rfl
    rw [helem, ← happ2]
    exact congr($(hι₂).app _ (verticalOneSimplex xnb))
  obtain ⟨F, hF⟩ :=
    exists_extension_of_unionProd_boundary_face_one φ₀ hspec
  refine ⟨F, ?_, ?_, ?_⟩
  · have e₂ : (∂Δ[n].ι ▷ Δ[1]) =
        Subcomplex.unionProd.ι₂ ∂Δ[n] (stdSimplex.face {1}) ≫
          (prismTgtInitial n).ι :=
      (Subcomplex.unionProd.ι₂_ι ∂Δ[n]
        (stdSimplex.face {1})).symm
    rw [e₂, Category.assoc, hF, hι₂]
  · apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro s
    have hmemFace : ((prismSectionAt (Δ[n] : SSet.{u})
          (1 : Fin 2)).app
          U s).2 ∈ (stdSimplex.face {1}).obj U := by
      change Finset.image
          (stdSimplex.objEquiv
            (((prismSectionAt (Δ[n] : SSet.{u}) (1 : Fin 2)).app
              U s).2)).toOrderHom
            ⊤ ≤ ({1} : Finset (Fin 2))
      rw [Finset.image_subset_iff]
      intro k _
      exact Finset.mem_singleton.2
        (asOrderHom_prismSectionAt_app_snd (Δ[n] : SSet.{u})
          (1 : Fin 2) s k)
    have hmem : (prismSectionAt (Δ[n] : SSet.{u}) 1).app U s ∈
        (prismTgtInitial n).obj U :=
      (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl hmemFace)
    set sface : (Δ[n] ⊗
          ((stdSimplex.face {1} :
            (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u})).obj U :=
      (s, ⟨((prismSectionAt (Δ[n] : SSet.{u}) 1).app U s).2,
        hmemFace⟩) with hsface
    have happ1 : (Subcomplex.unionProd.ι₁ ∂Δ[n]
          (stdSimplex.face {1})).app U sface =
        ⟨(prismSectionAt (Δ[n] : SSet.{u}) 1).app U s, hmem⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · exact (prismSectionAt_app_fst _ _ s).symm
      · rfl
    change F.app U ((prismSectionAt (Δ[n] : SSet.{u}) 1).app U s) =
      g.app U s
    have step1 : F.app U
          ((prismSectionAt (Δ[n] : SSet.{u}) 1).app U s) =
        φ₀.app U
          ⟨(prismSectionAt (Δ[n] : SSet.{u}) 1).app U s, hmem⟩ :=
      congr($(hF).app U
        ⟨(prismSectionAt (Δ[n] : SSet.{u}) 1).app U s, hmem⟩)
    have step2 : φ₀.app U
          ⟨(prismSectionAt (Δ[n] : SSet.{u}) 1).app U s, hmem⟩ =
        gface.app U sface := by
      rw [← happ1]
      exact congr($(hι₁).app U sface)
    have step3 : gface.app U sface = g.app U s := rfl
    rw [step1, step2, step3]
  · intro x
    set xb : ((∂Δ[n] : SSet.{u})) _⦋0⦌ :=
      ⟨x, vertex_mem_boundary_of_one_le hn x⟩ with hxb
    have hmemV : verticalOneSimplex x ∈
        (prismTgtInitial n).obj _ :=
      (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inr (by
        rw [verticalOneSimplex_fst]
        exact sigma_zero_mem_boundary_of_one_le hn x))
    have happ2' : (Subcomplex.unionProd.ι₂ ∂Δ[n]
          (stdSimplex.face {1})).app _
          (verticalOneSimplex xb) =
        ⟨verticalOneSimplex x, hmemV⟩ := by
      apply Subtype.ext
      change (∂Δ[n].ι ▷ Δ[1]).app _ (verticalOneSimplex xb) =
        verticalOneSimplex x
      have happx : (∂Δ[n].ι).app _ xb = x := rfl
      rw [whiskerRight_app_verticalOneSimplex, happx]
    refine (Edge.isEquivalence_iff_of_edge_eq ?_).2 (hVert xb)
    change F.app _ (verticalOneSimplex x) =
      H.app _ (verticalOneSimplex xb)
    calc F.app _ (verticalOneSimplex x)
        = φ₀.app _ ⟨verticalOneSimplex x, hmemV⟩ :=
          congr($(hF).app _ ⟨verticalOneSimplex x, hmemV⟩)
      _ = H.app _ (verticalOneSimplex xb) := by
          rw [← happ2']
          exact congr($(hι₂).app _ (verticalOneSimplex xb))

end PrismOneCellBridge

/-!
## Verticals are vertex evaluations (§2)

Evaluation at `Δ[0]` on a prism simplex over `Δ[0]` is the
vertical simplex value, through `curry_pre_app` and
`curry_unitIsoSelf`; consequently the verticals of
`ihomPrismOfSimplex e.edge` are the vertex evaluations of
`e`, hence equivalences when `e` is
(`Edge.IsEquivalence.eval_vertex`). This is the
`evalDeltaZeroIso`-at-`⦋1⦌` identification of the additional comparison obligation.
-/

section EvalVertical

variable {A C : SSet.{u}}

/-- The classifying map of the vertical simplex over `Δ[0]`
is the left-unitor inverse followed by whiskering the unit
isomorphism inverse: both maps `Δ[1] ⟶ Δ[0] ⊗ Δ[1]` have
first projection into the terminal `Δ[0]` and second
projection the identity (`whiskerRight_snd`,
`leftUnitor_hom`). -/
private lemma yonedaEquiv_symm_verticalOneSimplex_deltaZero :
    yonedaEquiv.symm
        (verticalOneSimplex (B := (Δ[0] : SSet.{u}))
          (stdSimplex.obj₀Equiv.symm 0)) =
      (λ_ (Δ[1] : SSet.{u})).inv ≫
        (Δ0IsoUnit.inv ▷ Δ[1]) := by
  apply CartesianMonoidalCategory.hom_ext
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _
  · have hc : yonedaEquiv.symm
          (verticalOneSimplex (B := (Δ[0] : SSet.{u}))
            (stdSimplex.obj₀Equiv.symm 0)) ≫
          CartesianMonoidalCategory.snd _ _ = 𝟙 Δ[1] := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
      rfl
    have hd : ((λ_ (Δ[1] : SSet.{u})).inv ≫
          (Δ0IsoUnit.inv ▷ Δ[1])) ≫
          CartesianMonoidalCategory.snd _ _ = 𝟙 Δ[1] := by
      rw [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
        ← CartesianMonoidalCategory.leftUnitor_hom, Iso.inv_hom_id]
    rw [hc, hd]

/-- **Evaluation at `Δ[0]` on a prism simplex is the vertical
value.** For `F₀ : Δ[0] ⊗ Δ[1] ⟶ C`, evaluating
`ihomSimplexOfPrism F₀` at `Δ[0]` gives `F₀` at the vertical
simplex over the unique vertex. After Yoneda both sides are
`(λ_ Δ[1]).inv ≫ (Δ0IsoUnit.inv ▷ Δ[1]) ≫ F₀`, by
`evalDeltaZeroIso_hom`, `curry_pre_app` and
`curry_unitIsoSelf` on one side and the classifying-map
computation on the other. -/
lemma evalDeltaZeroIso_hom_app_ihomSimplexOfPrism_one
    (F₀ : (Δ[0] : SSet.{u}) ⊗ Δ[1] ⟶ C) :
    ((evalDeltaZeroIso C).hom).app _ (ihomSimplexOfPrism F₀) =
      F₀.app _
        (verticalOneSimplex (stdSimplex.obj₀Equiv.symm 0)) := by
  apply yonedaEquiv.symm.injective
  have hL : yonedaEquiv.symm
        (((evalDeltaZeroIso C).hom).app _
          (ihomSimplexOfPrism F₀)) =
      (λ_ (Δ[1] : SSet.{u})).inv ≫
        (Δ0IsoUnit.inv ▷ Δ[1]) ≫ F₀ := by
    have e2 : yonedaEquiv.symm
          (((evalDeltaZeroIso C).hom).app _
            (ihomSimplexOfPrism F₀)) =
        MonoidalClosed.curry F₀ ≫ (evalDeltaZeroIso C).hom := by
      apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply,
        ihomSimplexOfPrism]
    rw [e2, evalDeltaZeroIso_hom, ← Category.assoc,
      MonoidalClosed.curry_pre_app, curry_unitIsoSelf]
  have hR : yonedaEquiv.symm
        (F₀.app _
          (verticalOneSimplex (stdSimplex.obj₀Equiv.symm 0))) =
      (λ_ (Δ[1] : SSet.{u})).inv ≫
        (Δ0IsoUnit.inv ▷ Δ[1]) ≫ F₀ := by
    have e : yonedaEquiv.symm
          (F₀.app _
            (verticalOneSimplex (stdSimplex.obj₀Equiv.symm 0))) =
        yonedaEquiv.symm
            (verticalOneSimplex (stdSimplex.obj₀Equiv.symm 0)) ≫
          F₀ := by
      apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    rw [e, yonedaEquiv_symm_verticalOneSimplex_deltaZero,
      Category.assoc]
  rw [hL, hR]

/-- The vertical of the prism of an edge `e` at a vertex `x`
is the vertex evaluation of `e` at `x`: precompose with the
vertex map, evaluate at `Δ[0]`, and apply the previous lemma
to the restricted prism. -/
lemma ihomPrismOfSimplex_app_verticalOneSimplex
    {a₀ a₁ : ((ihom A).obj C) _⦋0⦌} (e : Edge a₀ a₁)
    (x : A _⦋0⦌) :
    (ihomPrismOfSimplex e.edge).app _ (verticalOneSimplex x) =
      ((e.map ((pre (yonedaEquiv.symm x)).app C)).map
        (evalDeltaZeroIso C).hom).edge := by
  have hv : (yonedaEquiv.symm x).app _
      (stdSimplex.obj₀Equiv.symm 0) = x := by
    have h0 : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
      apply stdSimplex.obj₀Equiv.injective
      rfl
    rw [h0]
    exact yonedaEquiv_symm_app_id x
  calc (ihomPrismOfSimplex e.edge).app _ (verticalOneSimplex x)
      = ((yonedaEquiv.symm x ▷ Δ[1]) ≫
          ihomPrismOfSimplex e.edge).app _
          (verticalOneSimplex (stdSimplex.obj₀Equiv.symm 0)) := by
        change (ihomPrismOfSimplex e.edge).app _
            (verticalOneSimplex x) =
          (ihomPrismOfSimplex e.edge).app _
            ((yonedaEquiv.symm x ▷ Δ[1]).app _
              (verticalOneSimplex (stdSimplex.obj₀Equiv.symm 0)))
        rw [whiskerRight_app_verticalOneSimplex, hv]
    _ = ((evalDeltaZeroIso C).hom).app _
          (ihomSimplexOfPrism
            ((yonedaEquiv.symm x ▷ Δ[1]) ≫
              ihomPrismOfSimplex e.edge)) :=
        (evalDeltaZeroIso_hom_app_ihomSimplexOfPrism_one _).symm
    _ = ((e.map ((pre (yonedaEquiv.symm x)).app C)).map
          (evalDeltaZeroIso C).hom).edge := by
        rw [Edge.map_edge, Edge.map_edge,
          ← ihomSimplexOfPrism_pre_app,
          ihomSimplexOfPrism_ihomPrismOfSimplex]

/-- **Verticals of an equivalence-edge prism are
equivalences**, by identification with vertex evaluations
(`Edge.IsEquivalence.eval_vertex`, the supporting results). -/
lemma prismOneVerticalsEquivalences_ihomPrismOfSimplex_of_isEquivalence
    {a₀ a₁ : ((ihom A).obj C) _⦋0⦌} (e : Edge a₀ a₁)
    (he : e.IsEquivalence) :
    PrismOneVerticalsEquivalences (ihomPrismOfSimplex e.edge) := by
  intro x
  refine (Edge.isEquivalence_iff_of_edge_eq (e :=
      Edge.mk' ((ihomPrismOfSimplex e.edge).app _
        (verticalOneSimplex x))) (e' :=
      (e.map ((pre (yonedaEquiv.symm x)).app C)).map
        (evalDeltaZeroIso C).hom) ?_).2
    (he.eval_vertex (yonedaEquiv.symm x))
  change (ihomPrismOfSimplex e.edge).app _ (verticalOneSimplex x) =
    ((e.map ((pre (yonedaEquiv.symm x)).app C)).map
      (evalDeltaZeroIso C).hom).edge
  exact ihomPrismOfSimplex_app_verticalOneSimplex e x

end EvalVertical

/-!
## Skeletal closure: pushouts (§3)

The two `Δ[1]` properties are the cases `κ = 0, 1` of a single
vertex-indexed property, whose skeletal closures are proved
once. Vertices of a pushout come from the two sides
(evaluation at `⦋0⦌` preserves pushouts and coprojections in
`Type` are jointly surjective), prisms glue along
`(tensorRight Δ[1]).map_isPushout`, and sections glue by
`IsPushout.hom_ext` through section naturality.
-/

section SkeletalPushout

variable {A B C D X Y : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X}
  {f' : B ⟶ Y} {j : X ⟶ Y} {κ : Fin 2}

/-- `Δ[1]`-prism extension along `i` with prescribed section
at the vertex `κ` of `Δ[1]`: the common form of
`PrismSrcExtension` (`κ = 0`) and `PrismTgtExtension`
(`κ = 1`). -/
def PrismOneExtensionAt (κ : Fin 2) (i : A ⟶ B) (C : SSet.{u}) :
    Prop :=
  ∀ (H : A ⊗ Δ[1] ⟶ C) (g : B ⟶ C),
    prismSectionAt A κ ≫ H = i ≫ g →
    PrismOneVerticalsEquivalences H →
      ∃ F : B ⊗ Δ[1] ⟶ C,
        (i ▷ Δ[1]) ≫ F = H ∧ prismSectionAt B κ ≫ F = g ∧
          PrismOneVerticalsEquivalences F

lemma prismSrcExtension_iff_oneExtensionAt_zero :
    PrismSrcExtension i C ↔ PrismOneExtensionAt 0 i C :=
  Iff.rfl

lemma prismTgtExtension_iff_oneExtensionAt_one :
    PrismTgtExtension i C ↔ PrismOneExtensionAt 1 i C :=
  Iff.rfl

/-- Vertices of a pushout of simplicial sets come from the
two sides: evaluation at `⦋0⦌` preserves the pushout, and
the legs of a colimit cocone in `Type` are jointly
surjective, with the span apex mapping through either side. -/
lemma exists_app_eq_zero_of_isPushout (sq : IsPushout i f f' j)
    (y : Y _⦋0⦌) :
    (∃ b : B _⦋0⦌, f'.app _ b = y) ∨
      (∃ x : X _⦋0⦌, j.app _ x = y) := by
  obtain ⟨jj, y0, hy⟩ :=
    CategoryTheory.Limits.Types.jointly_surjective_of_isColimit
      ((sq.map ((evaluation SimplexCategoryᵒᵖ (Type u)).obj
        (op ⦋0⦌))).isColimit) y
  cases jj with
  | none => exact Or.inl ⟨i.app _ y0, hy⟩
  | some p =>
    cases p with
    | left => exact Or.inl ⟨y0, hy⟩
    | right => exact Or.inr ⟨y0, hy⟩

/-- **Prism extension is stable under cobase change:**
`PrismOneExtensionAt κ i C` implies
`PrismOneExtensionAt κ j C` for the cobase change `j` of `i`.
Restrict the data to `i`, extend there, glue the two prisms
along the tensored pushout, glue the sections by
`IsPushout.hom_ext`, and read verticals off the pieces at
vertices coming from either side. -/
theorem PrismOneExtensionAt.of_isPushout (sq : IsPushout i f f' j)
    (h : PrismOneExtensionAt κ i C) :
    PrismOneExtensionAt κ j C := by
  intro H g hagree hVert
  have hagreei : prismSectionAt A κ ≫ ((f ▷ Δ[1]) ≫ H) =
      i ≫ (f' ≫ g) := by
    calc prismSectionAt A κ ≫ ((f ▷ Δ[1]) ≫ H)
        = f ≫ (prismSectionAt X κ ≫ H) := by
          rw [← Category.assoc, prismSectionAt_comp_whiskerRight,
            Category.assoc]
      _ = (f ≫ j) ≫ g := by rw [hagree, Category.assoc]
      _ = (i ≫ f') ≫ g := by rw [sq.w]
      _ = i ≫ (f' ≫ g) := Category.assoc i f' g
  obtain ⟨F₁, hF₁r, hF₁s, hF₁v⟩ := h ((f ▷ Δ[1]) ≫ H) (f' ≫ g)
    hagreei (prismOneVerticalsEquivalences_whiskerRight_comp f H
      hVert)
  set sq₁ := (tensorRight Δ[1]).map_isPushout sq with hsq₁
  set F := sq₁.desc F₁ H hF₁r with hF
  have hFf' : (f' ▷ Δ[1]) ≫ F = F₁ := sq₁.inl_desc F₁ H hF₁r
  have hFj : (j ▷ Δ[1]) ≫ F = H := sq₁.inr_desc F₁ H hF₁r
  refine ⟨F, hFj, ?_, ?_⟩
  · apply sq.hom_ext
    · calc f' ≫ (prismSectionAt Y κ ≫ F)
          = prismSectionAt B κ ≫ ((f' ▷ Δ[1]) ≫ F) := by
            rw [← Category.assoc,
              ← prismSectionAt_comp_whiskerRight, Category.assoc]
        _ = f' ≫ g := by rw [hFf', hF₁s]
    · calc j ≫ (prismSectionAt Y κ ≫ F)
          = prismSectionAt X κ ≫ ((j ▷ Δ[1]) ≫ F) := by
            rw [← Category.assoc,
              ← prismSectionAt_comp_whiskerRight, Category.assoc]
        _ = j ≫ g := by rw [hFj, hagree]
  · intro y
    rcases exists_app_eq_zero_of_isPushout sq y with
      ⟨b, hb⟩ | ⟨x, hx⟩
    · refine (Edge.isEquivalence_iff_of_edge_eq (e :=
          Edge.mk' (F.app _ (verticalOneSimplex y))) (e' :=
          Edge.mk' (F₁.app _ (verticalOneSimplex b))) ?_).2
        (hF₁v b)
      change F.app _ (verticalOneSimplex y) =
        F₁.app _ (verticalOneSimplex b)
      calc F.app _ (verticalOneSimplex y)
          = ((f' ▷ Δ[1]) ≫ F).app _ (verticalOneSimplex b) := by
            change F.app _ (verticalOneSimplex y) =
              F.app _ ((f' ▷ Δ[1]).app _
                (verticalOneSimplex b))
            rw [whiskerRight_app_verticalOneSimplex, hb]
        _ = F₁.app _ (verticalOneSimplex b) :=
            congr($(hFf').app _ (verticalOneSimplex b))
    · refine (Edge.isEquivalence_iff_of_edge_eq (e :=
          Edge.mk' (F.app _ (verticalOneSimplex y))) (e' :=
          Edge.mk' (H.app _ (verticalOneSimplex x))) ?_).2
        (hVert x)
      change F.app _ (verticalOneSimplex y) =
        H.app _ (verticalOneSimplex x)
      calc F.app _ (verticalOneSimplex y)
          = ((j ▷ Δ[1]) ≫ F).app _ (verticalOneSimplex x) := by
            change F.app _ (verticalOneSimplex y) =
              F.app _ ((j ▷ Δ[1]).app _
                (verticalOneSimplex x))
            rw [whiskerRight_app_verticalOneSimplex, hx]
        _ = H.app _ (verticalOneSimplex x) :=
            congr($(hFj).app _ (verticalOneSimplex x))

/-- Source-prescribed prism extension is stable under cobase
change. -/
theorem PrismSrcExtension.of_isPushout (sq : IsPushout i f f' j)
    (h : PrismSrcExtension i C) :
    PrismSrcExtension j C :=
  prismSrcExtension_iff_oneExtensionAt_zero.2
    (PrismOneExtensionAt.of_isPushout sq
      (prismSrcExtension_iff_oneExtensionAt_zero.1 h))

/-- Target-prescribed prism extension is stable under cobase
change. -/
theorem PrismTgtExtension.of_isPushout (sq : IsPushout i f f' j)
    (h : PrismTgtExtension i C) :
    PrismTgtExtension j C :=
  prismTgtExtension_iff_oneExtensionAt_one.2
    (PrismOneExtensionAt.of_isPushout sq
      (prismTgtExtension_iff_oneExtensionAt_one.1 h))

end SkeletalPushout

/-!
## One-step cell attachments (§3, proven frontier)

Combining the unconditional cell bridges of §2 with cobase
stability gives source/target prism extension along any
single-cell attachment (a pushout of a boundary inclusion).
The `Δ[2]` analogues along a cell attachment would require
the pushout closure for `PrismTwoHornZero/TwoExtension`,
which is part of the additional comparison obligation below and is *not* proved in
this module; for `Δ[2]` the proven frontier is the boundary
inclusion itself, conditional on the cell shuffle inputs.
-/

section CellAttachments

variable {n : ℕ} {C X Y : SSet.{u}}
  {f : (∂Δ[n] : SSet.{u}) ⟶ X} {f' : Δ[n] ⟶ Y} {j : X ⟶ Y}

/-- **Source-prescribed prism extension along a single-cell
attachment**, unconditionally: the cell bridge
(`prismSrcExtension_boundary`, from the supporting result) transported along
the attaching pushout. -/
theorem prismSrcExtension_of_isPushout_boundary
    [Quasicategory C] (sq : IsPushout ∂Δ[n].ι f f' j) :
    PrismSrcExtension j C :=
  PrismSrcExtension.of_isPushout sq prismSrcExtension_boundary

/-- **Target-prescribed prism extension along a single-cell
attachment**, unconditionally (the mirror). -/
theorem prismTgtExtension_of_isPushout_boundary
    [Quasicategory C] (sq : IsPushout ∂Δ[n].ι f f' j) :
    PrismTgtExtension j C :=
  PrismTgtExtension.of_isPushout sq prismTgtExtension_boundary

end CellAttachments

end SSet

end
