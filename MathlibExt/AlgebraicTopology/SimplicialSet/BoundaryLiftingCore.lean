/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.DescentProp412
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Left fibrations and simplicial boundary geometry

Left fibrations of simplicial sets are defined by the right lifting property against
all horns with nonfinal missing vertex, including the left outer horns in dimension
one. They are stable under base change, and their vertex fibers have fillers for
these same horns.

The boundary of a simplex is the union of its left outer horn and back face; their
intersection is the boundary of the back face, and the inclusions form a pushout.
For an arbitrary simplicial map, a left mapping space is a pullback of the corresponding
under-slice comparison. Lifting properties of the comparison therefore pass to the
mapping-space map under the stated hypotheses.

Categorical equivalence alone over a pre-fibrant base does not imply that these naive
mapping-space maps are trivial Kan fibrations. See Lurie, Higher Topos Theory,
Definition 2.0.0.3, Proposition 2.1.2.1, and Lemma 2.1.3.4, and Campbell,
A counterexample in quasi-category theory, arXiv:1904.04965v3.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite MorphismProperty
open scoped Simplicial

universe u

namespace SSet

variable {X Y S T E B : SSet.{u}}

/-!
## Left horn inclusions and their lifting class

For `Λ[n,i] → Δ[n]` with `i` not the last vertex, the right lifting class is the
class of left fibrations. It contains the right lifting conditions for all inner
horns together with the left outer horn in every positive dimension.
-/

/--
The family of horn inclusions `Λ[n + 1,i] → Δ[n + 1]` with `i` different from the
last vertex. It includes the left outer horns and all inner horns, including
`Λ[1,0] → Δ[1]`.
-/
inductive leftHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) :
    leftHornInclusions Λ[n + 1, i].ι

/--
For `i < Fin.last n`, the horn inclusion `Λ[n,i] → Δ[n]` belongs to the family
of left horn inclusions.
-/
lemma horn_ι_mem_leftHornInclusions {n : ℕ} {i : Fin (n + 1)}
    (hi : i < Fin.last n) : leftHornInclusions (horn.{u} n i).ι := by
  obtain _ | k := n
  · grind
  · exact ⟨i, hi⟩

/--
Every inner horn inclusion belongs to the family of left horn inclusions.
-/
lemma innerHornInclusions_le_leftHornInclusions :
    innerHornInclusions.{u} ≤ leftHornInclusions := by
  intro _ _ _ h
  obtain @⟨n, i, -, hn⟩ := h
  exact ⟨i, hn⟩

/--
The morphism property consisting of simplicial maps with the right lifting
property against every nonfinal horn inclusion.
-/
def leftFibrations : MorphismProperty SSet.{u} := leftHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange,
  IsStableUnderRetracts

/--
A simplicial map with the right lifting property against all horns whose missing
vertex is not the last vertex, in every positive dimension.
-/
@[mk_iff]
class LeftFibration {X Y : SSet.{u}} (q : X ⟶ Y) : Prop where
  /--
  The right lifting property against the family of left horn inclusions for the
  given simplicial map.
  -/
  mem : leftFibrations q

/--
A map carrying a `LeftFibration` structure belongs to the right lifting class of
left horn inclusions.
-/
lemma mem_leftFibrations {X Y : SSet.{u}} (q : X ⟶ Y)
    [LeftFibration q] : leftFibrations q :=
  LeftFibration.mem

/--
The right lifting property against all left horn inclusions implies the right
lifting property against inner horn inclusions.
-/
lemma leftFibrations_le_innerFibrations :
    leftFibrations.{u} ≤ innerFibrations :=
  antitone_rlp innerHornInclusions_le_leftHornInclusions

/--
A left fibration is an inner fibration.
-/
theorem LeftFibration.innerFibration {q : X ⟶ Y} [LeftFibration q] :
    InnerFibration q :=
  ⟨leftFibrations_le_innerFibrations _ LeftFibration.mem⟩

instance (priority := 100) {q : X ⟶ Y} [LeftFibration q] :
    InnerFibration q :=
  LeftFibration.innerFibration

/--
A left fibration has the right lifting property against `Λ[n,i] → Δ[n]` whenever
`i < Fin.last n`.
-/
theorem LeftFibration.hasLiftingProperty_horn {p : X ⟶ S}
    [LeftFibration p] {n : ℕ} {i : Fin (n + 1)} (hi : i < Fin.last n) :
    HasLiftingProperty Λ[n, i].ι p :=
  LeftFibration.mem _ (horn_ι_mem_leftHornInclusions hi)

/--
A simplicial map is a left fibration if it lifts every horn with nonfinal missing
vertex, in every dimension.
-/
theorem leftFibration_of_hasLiftingProperty_horn {p : X ⟶ S}
    (h : ∀ {n : ℕ} {i : Fin (n + 1)}, i < Fin.last n →
      HasLiftingProperty Λ[n, i].ι p) :
    LeftFibration p := by
  refine ⟨fun _ _ _ hi => ?_⟩
  obtain @⟨n, i, hi⟩ := hi
  exact h hi

/--
A simplicial map with the right lifting property against the Kan–Quillen generating
boundary inclusions is a left fibration.
-/
theorem leftFibration_of_rlp_I {p : X ⟶ S}
    (hp : modelCategoryQuillen.I.rlp p) : LeftFibration p := by
  refine leftFibration_of_hasLiftingProperty_horn (fun {n i} _ => ?_)
  have hmono : monomorphisms SSet.{u} Λ[n, i].ι :=
    monomorphisms.infer_property _
  have hllp : modelCategoryQuillen.I.rlp.llp Λ[n, i].ι :=
    modelCategoryQuillen.llp_rlp_I ▸ hmono
  exact hllp _ hp

/--
In a pullback square, the base change of a left fibration is a left fibration.
-/
theorem leftFibration_of_isPullback {p : X ⟶ S} {f : S ⟶ T}
    {q : Y ⟶ T} {g : X ⟶ Y} (sq : IsPullback g p q f)
    [LeftFibration q] : LeftFibration p :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback sq
    LeftFibration.mem⟩

/--
For a left fibration `q : E → B` and a vertex `b : Δ[0] → B`, the projection
`pullback q b → Δ[0]` is a left fibration.
-/
instance leftFibration_pullback_snd (q : E ⟶ B) [LeftFibration q]
    (b : (Δ[0] : SSet.{u}) ⟶ B) : LeftFibration (pullback.snd q b) :=
  leftFibration_of_isPullback (IsPullback.of_hasPullback q b)

/--
Every horn with nonfinal missing vertex in the fiber of a left fibration over a
vertex extends to a simplex in that fiber.
-/
theorem LeftFibration.exists_hornFiller_fiber {q : E ⟶ B}
    [LeftFibration q] (b : (Δ[0] : SSet.{u}) ⟶ B) {n : ℕ}
    {i : Fin (n + 1)} (hi : i < Fin.last n)
    (σ₀ : (Λ[n, i] : SSet.{u}) ⟶ pullback q b) :
    ∃ σ : Δ[n] ⟶ pullback q b, Λ[n, i].ι ≫ σ = σ₀ := by
  have : HasLiftingProperty Λ[n, i].ι (pullback.snd q b) :=
    LeftFibration.hasLiftingProperty_horn hi
  let sq : CommSq σ₀ Λ[n, i].ι (pullback.snd q b)
      (toDeltaZero Δ[n]) := CommSq.mk (by
    rw [toDeltaZero_eq (σ₀ ≫ pullback.snd q b),
      toDeltaZero_eq (Λ[n, i].ι ≫ toDeltaZero Δ[n])])
  exact ⟨sq.lift, sq.fac_left⟩

/-!
## Simplex boundary as a horn and back face union

The boundary `∂Δ[n + 1]` is `Λ[n + 1,0] ∪ Δ[{1,…,n + 1}]`. The back face is
identified with `Δ[n]`, and the intersection with the left horn is its boundary
`∂Δ[n]`. Consequently, agreeing maps on the horn and the back face glue uniquely
across the boundary.
-/

/--
The boundary of `Δ[n + 1]` is the union of the left horn `Λ[n + 1,0]` and the
face opposite vertex zero, on vertices `{1,…,n + 1}`.
-/
theorem boundary_eq_horn_zero_sup_face (n : ℕ) :
    boundary.{u} (n + 1) =
      Λ[n + 1, (0 : Fin (n + 2))] ⊔
        stdSimplex.face {(0 : Fin (n + 2))}ᶜ := by
  rw [boundary_eq_iSup, horn_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    intro i
    by_cases hi : i = 0
    · subst hi
      exact le_sup_right
    · exact le_sup_of_le_left (le_iSup
        (fun j : ({(0 : Fin (n + 2))}ᶜ : Set (Fin (n + 2))) =>
          stdSimplex.face {j.1}ᶜ) ⟨i, by simp [hi]⟩)
  · apply sup_le
    · apply iSup_le
      intro j
      exact le_iSup (fun i : Fin (n + 2) => stdSimplex.face {i}ᶜ) j.1
    · exact le_iSup (fun i : Fin (n + 2) => stdSimplex.face {i}ᶜ) 0

/--
The horn `Λ[n + 1,0]` is a subcomplex of `∂Δ[n + 1]`.
-/
lemma horn_zero_le_boundary (n : ℕ) :
    Λ[n + 1, (0 : Fin (n + 2))] ≤ boundary.{u} (n + 1) := by
  rw [boundary_eq_horn_zero_sup_face]
  exact le_sup_left

/--
The intersection of `Λ[n + 1,0]` with the face opposite zero is the union of the
codimension-two faces omitting zero and another vertex `j ≠ 0`.
-/
theorem horn_zero_inf_face_eq_iSup (n : ℕ) :
    Λ[n + 1, (0 : Fin (n + 2))] ⊓
        stdSimplex.face {(0 : Fin (n + 2))}ᶜ =
      ⨆ (j : ({(0 : Fin (n + 2))}ᶜ : Set (Fin (n + 2)))),
        stdSimplex.face ({j.1}ᶜ ⊓ {(0 : Fin (n + 2))}ᶜ) := by
  rw [horn_eq_iSup, Subfunctor.iSup_min]
  exact iSup_congr fun j => stdSimplex.face_inter_face _ _

/--
The preimage of `Λ[n + 1,0]` under `d₀ : Δ[n] → Δ[n + 1]` is `∂Δ[n]`.
-/
theorem preimage_horn_zero_delta_zero (n : ℕ) :
    (Λ[n + 1, (0 : Fin (n + 2))]).preimage
        (stdSimplex.δ (0 : Fin (n + 2))) =
      boundary.{u} n := by
  ext ⟨d⟩ x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  have hcomp : ⇑(f ≫ SimplexCategory.δ (0 : Fin (n + 2))) =
      Fin.succAbove 0 ∘ ⇑f := rfl
  have hrange : Set.range (Fin.succAbove 0 ∘ ⇑f) ∪
        {(0 : Fin (n + 2))} = Set.univ ↔
      Set.range (⇑f) = Set.univ := by
    rw [Set.range_comp]
    constructor
    · intro h
      by_contra hs
      obtain ⟨k, hk⟩ := (Set.ne_univ_iff_exists_notMem _).mp hs
      have hne : Fin.succAbove 0 k ≠ (0 : Fin (n + 2)) := by
        intro h0
        have hmem : (0 : Fin (n + 2)) ∈
            Set.range (Fin.succAbove 0) := ⟨k, h0⟩
        rw [Fin.range_succAbove] at hmem
        exact hmem rfl
      have hnin : Fin.succAbove 0 k ∉
          Fin.succAbove 0 '' Set.range (⇑f) := by
        rintro ⟨y, hy, hyy⟩
        rw [← Fin.succAboveOrderEmb_apply,
          ← Fin.succAboveOrderEmb_apply] at hyy
        exact hk ((Fin.succAboveOrderEmb
          (0 : Fin (n + 2))).injective hyy ▸ hy)
      have hnout : Fin.succAbove 0 k ∉
          Fin.succAbove 0 '' Set.range (⇑f) ∪ {(0 : Fin (n + 2))} := by
        simp only [Set.mem_union, Set.mem_singleton_iff, not_or]
        exact ⟨hnin, hne⟩
      exact hnout (h ▸ Set.mem_univ _)
    · intro h
      rw [h, Set.image_univ, Fin.range_succAbove]
      exact Set.compl_union_self _
  simp only [Subcomplex.preimage_obj, Set.mem_preimage, mem_horn_iff, boundary,
    Set.mem_ofPred_eq, ← Set.range_eq_univ]
  exact not_congr hrange

/--
The preimage of the face opposite zero under its inclusion
`d₀ : Δ[n] → Δ[n + 1]` is all of `Δ[n]`.
-/
theorem preimage_face_zero_delta_zero (n : ℕ) :
    (stdSimplex.face {(0 : Fin (n + 2))}ᶜ).preimage
        (stdSimplex.δ (0 : Fin (n + 2))) =
      ⊤ := by
  ext ⟨d⟩ x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  have hcomp : ⇑(f ≫ SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom =
      Fin.succAbove 0 ∘ ⇑f.toOrderHom := rfl
  simp only [Subcomplex.preimage_obj, Set.mem_preimage,
    Subfunctor.top_obj, Set.mem_univ, iff_true,
    stdSimplex.face_obj, Set.mem_ofPred_eq]
  rw [Finset.image_subset_iff]
  intro a _
  simp only [Finset.mem_compl,
    Finset.mem_singleton]
  intro hcontra
  have hmem : (0 : Fin (n + 2)) ∈
      Set.range (Fin.succAbove 0) := ⟨f.toOrderHom a, hcontra⟩
  rw [Fin.range_succAbove] at hmem
  exact hmem rfl

/--
The intersection of the left horn and the back face pulls back under the back-face
inclusion to the boundary `∂Δ[n]`.
-/
theorem preimage_horn_zero_inf_face_delta_zero (n : ℕ) :
    (Λ[n + 1, (0 : Fin (n + 2))] ⊓
        stdSimplex.face {(0 : Fin (n + 2))}ᶜ).preimage
        (stdSimplex.δ (0 : Fin (n + 2))) =
      boundary.{u} n := by
  rw [Subcomplex.preimage_min, preimage_horn_zero_delta_zero,
    preimage_face_zero_delta_zero, inf_top_eq]

/--
The square of inclusions from the intersection of `Λ[n + 1,0]` and the back face
to those two pieces, and then to `∂Δ[n + 1]`, is a pushout square.
-/
theorem isPushout_boundary_hornZero_face (n : ℕ) :
    IsPushout
      (Subcomplex.homOfLE (inf_le_left :
        Λ[n + 1, (0 : Fin (n + 2))] ⊓
            stdSimplex.face {(0 : Fin (n + 2))}ᶜ ≤
          Λ[n + 1, (0 : Fin (n + 2))]))
      (Subcomplex.homOfLE (inf_le_right :
        Λ[n + 1, (0 : Fin (n + 2))] ⊓
            stdSimplex.face {(0 : Fin (n + 2))}ᶜ ≤
          stdSimplex.face {(0 : Fin (n + 2))}ᶜ))
      (Subcomplex.homOfLE (horn_zero_le_boundary n))
      (Subcomplex.homOfLE (face_singleton_compl_le_boundary
        (0 : Fin (n + 2)))) :=
  Subcomplex.BicartSq.isPushout
    ⟨(boundary_eq_horn_zero_sup_face n).symm, rfl⟩

/--
Maps from the left horn and the back face of `Δ[n + 1]` that agree on their
intersection glue uniquely to a map from `∂Δ[n + 1]`.
-/
theorem existsUnique_boundary_map_of_hornZero_face (n : ℕ)
    {Z : SSet.{u}}
    (u₁ : (Λ[n + 1, (0 : Fin (n + 2))] : SSet.{u}) ⟶ Z)
    (u₂ : (stdSimplex.face {(0 : Fin (n + 2))}ᶜ : SSet.{u}) ⟶ Z)
    (w : Subcomplex.homOfLE (inf_le_left :
        Λ[n + 1, (0 : Fin (n + 2))] ⊓
            stdSimplex.face {(0 : Fin (n + 2))}ᶜ ≤
          Λ[n + 1, (0 : Fin (n + 2))]) ≫ u₁ =
      Subcomplex.homOfLE (inf_le_right :
        Λ[n + 1, (0 : Fin (n + 2))] ⊓
            stdSimplex.face {(0 : Fin (n + 2))}ᶜ ≤
          stdSimplex.face {(0 : Fin (n + 2))}ᶜ) ≫ u₂) :
    ∃! u : ((boundary (n + 1) : (Δ[n + 1] : SSet.{u}).Subcomplex) :
        SSet.{u}) ⟶ Z,
      Subcomplex.homOfLE (horn_zero_le_boundary n) ≫ u = u₁ ∧
        Subcomplex.homOfLE (face_singleton_compl_le_boundary
          (0 : Fin (n + 2))) ≫ u = u₂ := by
  refine ⟨(isPushout_boundary_hornZero_face n).desc u₁ u₂ w,
    ⟨(isPushout_boundary_hornZero_face n).inl_desc u₁ u₂ w,
      (isPushout_boundary_hornZero_face n).inr_desc u₁ u₂ w⟩,
    fun u hu => (isPushout_boundary_hornZero_face n).hom_ext
      (hu.1.trans
        ((isPushout_boundary_hornZero_face n).inl_desc u₁ u₂ w).symm)
      (hu.2.trans
        ((isPushout_boundary_hornZero_face n).inr_desc u₁ u₂ w).symm)⟩

/--
The vertex of `X` obtained by evaluating a map `∂Δ[n + 1] → X` at vertex zero,
viewed as a simplicial map `Δ[0] → X`.
-/
def boundaryVertexZero {n : ℕ} {X : SSet.{u}}
    (u : ((boundary (n + 1) : (Δ[n + 1] : SSet.{u}).Subcomplex) :
      SSet.{u}) ⟶ X) :
    (Δ[0] : SSet.{u}) ⟶ X :=
  SSet.const (u.app (op ⦋0⦌)
    ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), by
      rw [boundary_obj_eq_univ 0 (n + 1) (Nat.zero_lt_succ n)]
      exact Set.mem_univ _⟩)

/-!
## Left mapping spaces and under-slice comparison pullbacks

For `p : X → S` and vertices `x,y` of `X`, the left mapping space `Homᴸ_X(x,y)`
is the pullback of `X_(x/) → S_(px/) ×_S X` along the map from `Homᴸ_S(px,py)`
whose under-slice component is the canonical inclusion and whose `X` component is
constant at `y`. This identification holds without a fibrancy assumption on `p`.
-/

/--
A map `b : Δ[0] → Z`, evaluated after the unique map to `Δ[0]`, gives the constant
simplex at `b` in every simplicial degree.
-/
lemma toDeltaZero_comp_app {Z M : SSet.{u}}
    (b : (Δ[0] : SSet.{u}) ⟶ Z) {n : SimplexCategoryᵒᵖ}
    (t : M.obj n) :
    b.app n ((toDeltaZero M).app n t) =
      SSet.yonedaEquiv (toDeltaZero (SSet.stdSimplex.obj n.unop) ≫ b) := by
  rw [← toDeltaZero_eq
    (SSet.yonedaEquiv.symm ((toDeltaZero M).app n t)),
    yonedaEquiv_comp, Equiv.apply_symm_apply]

/--
The composite `Homᴸ_Z(a,b) → Z_(a/) → Z` is the constant simplicial map at the
target vertex `b`.
-/
lemma mappingSpaceLeft_toSliceUnder_proj (Z : SSet.{u})
    (a b : (Δ[0] : SSet.{u}) ⟶ Z) :
    mappingSpaceLeft.toSliceUnder Z a b ≫ sliceUnder.proj Z a =
      toDeltaZero (mappingSpaceLeft Z a b) ≫ b := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  simp only [NatTrans.comp_app, types_comp_apply]
  rw [mappingSpaceLeft.proj_toSliceUnder_apply, toDeltaZero_comp_app]

/--
For `p : X → S` and vertices `x,y` of `X`, the map from `Homᴸ_S(px,py)` to
`S_(px/) ×_S X` whose first component is the under-slice inclusion and second
component is the constant map at `y`.
-/
noncomputable def mappingSpaceLeftToPullback {p : X ⟶ S}
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    mappingSpaceLeft S (x ≫ p) (y ≫ p) ⟶
      pullback (sliceUnder.proj S (x ≫ p)) p :=
  pullback.lift (mappingSpaceLeft.toSliceUnder S (x ≫ p) (y ≫ p))
    (toDeltaZero (mappingSpaceLeft S (x ≫ p) (y ≫ p)) ≫ y)
    (by rw [mappingSpaceLeft_toSliceUnder_proj, Category.assoc])

/--
The first projection of `mappingSpaceLeftToPullback` is the inclusion of the
target left mapping space into the under-slice `S_(px/)`.
-/
@[reassoc (attr := simp)]
theorem mappingSpaceLeftToPullback_fst {p : X ⟶ S}
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    mappingSpaceLeftToPullback (p := p) x y ≫
        pullback.fst (sliceUnder.proj S (x ≫ p)) p =
      mappingSpaceLeft.toSliceUnder S (x ≫ p) (y ≫ p) :=
  pullback.lift_fst _ _ _

/--
The second projection of `mappingSpaceLeftToPullback` is the constant simplicial
map at the vertex `y` of `X`.
-/
@[reassoc (attr := simp)]
theorem mappingSpaceLeftToPullback_snd {p : X ⟶ S}
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    mappingSpaceLeftToPullback (p := p) x y ≫
        pullback.snd (sliceUnder.proj S (x ≫ p)) p =
      toDeltaZero (mappingSpaceLeft S (x ≫ p) (y ≫ p)) ≫ y :=
  pullback.lift_snd _ _ _

/--
The under-slice inclusion followed by the slice comparison equals the map induced
on left mapping spaces by `p` followed by the target mapping-space pullback map.
-/
theorem mappingSpaceLeft_comp_sliceUnderComparison {p : X ⟶ S}
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    mappingSpaceLeft.toSliceUnder X x y ≫
        sliceUnderComparison (p := p) x =
      mappingSpaceLeft.map X x y p ≫
        mappingSpaceLeftToPullback (p := p) x y := by
  apply pullback.hom_ext
  · simp only [Category.assoc, sliceUnderComparison_fst,
      mappingSpaceLeftToPullback_fst, mappingSpaceLeft.map_toSliceUnder]
  · rw [Category.assoc, Category.assoc, sliceUnderComparison_snd,
      mappingSpaceLeftToPullback_snd,
      mappingSpaceLeft_toSliceUnder_proj, ← Category.assoc,
      toDeltaZero_eq (mappingSpaceLeft.map X x y p ≫
        toDeltaZero (mappingSpaceLeft S (x ≫ p) (y ≫ p)))]

/--
The second pullback projection of the slice comparison at a simplex is its
under-slice projection in `X`.
-/
lemma pullback_snd_app_sliceUnderComparison_app {p : X ⟶ S}
    (x : (Δ[0] : SSet.{u}) ⟶ X) {n : SimplexCategoryᵒᵖ}
    (w : (sliceUnder X x).obj n) :
    (pullback.snd (sliceUnder.proj S (x ≫ p)) p).app n
        ((sliceUnderComparison (p := p) x).app n w) =
      (sliceUnder.proj X x).app n w :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (sliceUnderComparison_snd (p := p) x) n) w

/--
The first pullback projection of the slice comparison at a simplex is its
under-slice image under `p : X → S`.
-/
lemma pullback_fst_app_sliceUnderComparison_app {p : X ⟶ S}
    (x : (Δ[0] : SSet.{u}) ⟶ X) {n : SimplexCategoryᵒᵖ}
    (w : (sliceUnder X x).obj n) :
    (pullback.fst (sliceUnder.proj S (x ≫ p)) p).app n
        ((sliceUnderComparison (p := p) x).app n w) =
      (sliceUnder.map X x p).app n w :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (sliceUnderComparison_fst (p := p) x) n) w

/--
The second projection of the image of a target left mapping-space simplex is the
constant simplex at `y`.
-/
lemma pullback_snd_app_mappingSpaceLeftToPullback_app
    {p : X ⟶ S} (x y : (Δ[0] : SSet.{u}) ⟶ X)
    {n : SimplexCategoryᵒᵖ}
    (w : (mappingSpaceLeft S (x ≫ p) (y ≫ p)).obj n) :
    (pullback.snd (sliceUnder.proj S (x ≫ p)) p).app n
        ((mappingSpaceLeftToPullback (p := p) x y).app n w) =
      y.app n
        ((toDeltaZero (mappingSpaceLeft S (x ≫ p) (y ≫ p))).app n w) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (mappingSpaceLeftToPullback_snd (p := p) x y) n) w

/--
The first projection of the image of a target left mapping-space simplex is its
inclusion into the under-slice of `S`.
-/
lemma pullback_fst_app_mappingSpaceLeftToPullback_app
    {p : X ⟶ S} (x y : (Δ[0] : SSet.{u}) ⟶ X)
    {n : SimplexCategoryᵒᵖ}
    (w : (mappingSpaceLeft S (x ≫ p) (y ≫ p)).obj n) :
    (pullback.fst (sliceUnder.proj S (x ≫ p)) p).app n
        ((mappingSpaceLeftToPullback (p := p) x y).app n w) =
      (mappingSpaceLeft.toSliceUnder S (x ≫ p) (y ≫ p)).app n w :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (mappingSpaceLeftToPullback_fst (p := p) x y) n) w

/--
For a simplex in the pullback of the slice comparison and the target mapping-space
map, its two projections have equal images in `S_(px/) ×_S X`.
-/
lemma sliceUnderComparison_app_fst_snd_eq {p : X ⟶ S}
    (x y : (Δ[0] : SSet.{u}) ⟶ X) {n : SimplexCategoryᵒᵖ}
    (z : (pullback (sliceUnderComparison (p := p) x)
      (mappingSpaceLeftToPullback (p := p) x y)).obj n) :
    (sliceUnderComparison (p := p) x).app n
        ((pullback.fst (sliceUnderComparison (p := p) x)
          (mappingSpaceLeftToPullback (p := p) x y)).app n z) =
      (mappingSpaceLeftToPullback (p := p) x y).app n
        ((pullback.snd (sliceUnderComparison (p := p) x)
          (mappingSpaceLeftToPullback (p := p) x y)).app n z) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (pullback.condition
      (f := sliceUnderComparison (p := p) x)
      (g := mappingSpaceLeftToPullback (p := p) x y)) n) z
  simpa only [NatTrans.comp_app, types_comp_apply] using h

/--
The right join restriction of the under-slice simplex obtained from the first
pullback projection is the constant simplex at `y`.
-/
lemma joinInr_pullback_fst_app_eq {p : X ⟶ S}
    (x y : (Δ[0] : SSet.{u}) ⟶ X) {n : SimplexCategoryᵒᵖ}
    (z : (pullback (sliceUnderComparison (p := p) x)
      (mappingSpaceLeftToPullback (p := p) x y)).obj n) :
    SSet.joinInr Δ[0] (SSet.stdSimplex.obj n.unop) ≫
        ((pullback.fst (sliceUnderComparison (p := p) x)
          (mappingSpaceLeftToPullback (p := p) x y)).app n z).1 =
      toDeltaZero (SSet.stdSimplex.obj n.unop) ≫ y := by
  apply SSet.yonedaEquiv.injective
  have h2 : (sliceUnder.proj X x).app n
        ((pullback.fst (sliceUnderComparison (p := p) x)
          (mappingSpaceLeftToPullback (p := p) x y)).app n z) =
      y.app n ((toDeltaZero
          (mappingSpaceLeft S (x ≫ p) (y ≫ p))).app n
        ((pullback.snd (sliceUnderComparison (p := p) x)
          (mappingSpaceLeftToPullback (p := p) x y)).app n z)) := by
    rw [← pullback_snd_app_sliceUnderComparison_app,
      ← pullback_snd_app_mappingSpaceLeftToPullback_app]
    exact congrArg ((pullback.snd (sliceUnder.proj S (x ≫ p)) p).app n)
      (sliceUnderComparison_app_fst_snd_eq x y z)
  rwa [sliceUnder.proj_apply, toDeltaZero_comp_app] at h2

/--
The underlying join map of the first pullback projection, postcomposed with `p`,
equals the join map represented by the second pullback projection.
-/
lemma pullback_fst_app_val_comp_p_eq {p : X ⟶ S}
    (x y : (Δ[0] : SSet.{u}) ⟶ X) {n : SimplexCategoryᵒᵖ}
    (z : (pullback (sliceUnderComparison (p := p) x)
      (mappingSpaceLeftToPullback (p := p) x y)).obj n) :
    ((pullback.fst (sliceUnderComparison (p := p) x)
        (mappingSpaceLeftToPullback (p := p) x y)).app n z).1 ≫ p =
      ((pullback.snd (sliceUnderComparison (p := p) x)
        (mappingSpaceLeftToPullback (p := p) x y)).app n z).1 := by
  have h2 : (sliceUnder.map X x p).app n
        ((pullback.fst (sliceUnderComparison (p := p) x)
          (mappingSpaceLeftToPullback (p := p) x y)).app n z) =
      (mappingSpaceLeft.toSliceUnder S (x ≫ p) (y ≫ p)).app n
        ((pullback.snd (sliceUnderComparison (p := p) x)
          (mappingSpaceLeftToPullback (p := p) x y)).app n z) := by
    rw [← pullback_fst_app_sliceUnderComparison_app,
      ← pullback_fst_app_mappingSpaceLeftToPullback_app]
    exact congrArg ((pullback.fst (sliceUnder.proj S (x ≫ p)) p).app n)
      (sliceUnderComparison_app_fst_snd_eq x y z)
  have h3 := congrArg Subtype.val h2
  simpa only [sliceUnder.map_app_val,
    mappingSpaceLeft.toSliceUnder_app_val] using h3

/--
The simplicial isomorphism
`Homᴸ_X(x,y) ≅ pullback (sliceUnderComparison p x) (mappingSpaceLeftToPullback x y)`.
A simplex on either side is a join map with left endpoint `x`, right face constant
at `y`, and the specified image under `p`.
-/
noncomputable def mappingSpaceLeftIsoPullback {p : X ⟶ S}
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    mappingSpaceLeft X x y ≅
      pullback (sliceUnderComparison (p := p) x)
        (mappingSpaceLeftToPullback (p := p) x y) where
  hom := pullback.lift (mappingSpaceLeft.toSliceUnder X x y)
    (mappingSpaceLeft.map X x y p)
    (mappingSpaceLeft_comp_sliceUnderComparison x y)
  inv := {
    app := fun n => ↾fun z =>
      ⟨((pullback.fst (sliceUnderComparison (p := p) x)
          (mappingSpaceLeftToPullback (p := p) x y)).app n z).1,
        ((pullback.fst (sliceUnderComparison (p := p) x)
          (mappingSpaceLeftToPullback (p := p) x y)).app n z).2,
        joinInr_pullback_fst_app_eq x y z⟩
    naturality := by
      intro n m α
      apply ConcreteCategory.hom_ext
      intro z
      apply Subtype.ext
      have hnat : (pullback.fst (sliceUnderComparison (p := p) x)
            (mappingSpaceLeftToPullback (p := p) x y)).app m
            ((pullback (sliceUnderComparison (p := p) x)
              (mappingSpaceLeftToPullback (p := p) x y)).map α z) =
          (sliceUnder X x).map α
            ((pullback.fst (sliceUnderComparison (p := p) x)
              (mappingSpaceLeftToPullback (p := p) x y)).app n z) :=
        ConcreteCategory.congr_hom
          ((pullback.fst (sliceUnderComparison (p := p) x)
            (mappingSpaceLeftToPullback (p := p) x y)).naturality α) z
      change ((pullback.fst (sliceUnderComparison (p := p) x)
            (mappingSpaceLeftToPullback (p := p) x y)).app m
          ((pullback (sliceUnderComparison (p := p) x)
            (mappingSpaceLeftToPullback (p := p) x y)).map α z)).1 =
        (SSet.join.obj Δ[0]).map (SSet.stdSimplex.map α.unop) ≫
          ((pullback.fst (sliceUnderComparison (p := p) x)
            (mappingSpaceLeftToPullback (p := p) x y)).app n z).1
      rw [hnat, sliceUnder.map_val] }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    have hf0 := ConcreteCategory.congr_hom
      (NatTrans.congr_app (pullback.lift_fst
        (mappingSpaceLeft.toSliceUnder X x y) (mappingSpaceLeft.map X x y p)
        (mappingSpaceLeft_comp_sliceUnderComparison x y)) n) σ
    simp only [NatTrans.comp_app, types_comp_apply] at hf0
    change ((pullback.fst (sliceUnderComparison (p := p) x)
        (mappingSpaceLeftToPullback (p := p) x y)).app n
        ((pullback.lift (mappingSpaceLeft.toSliceUnder X x y)
          (mappingSpaceLeft.map X x y p)
          (mappingSpaceLeft_comp_sliceUnderComparison x y)).app n σ)).1 =
      σ.1
    rw [hf0, mappingSpaceLeft.toSliceUnder_app_val]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro z
      apply Subtype.ext
      rfl
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro z
      apply Subtype.ext
      change ((pullback.fst (sliceUnderComparison (p := p) x)
          (mappingSpaceLeftToPullback (p := p) x y)).app n z).1 ≫ p =
        ((pullback.snd (sliceUnderComparison (p := p) x)
          (mappingSpaceLeftToPullback (p := p) x y)).app n z).1
      exact pullback_fst_app_val_comp_p_eq x y z

/--
For any simplicial map `p : X → S`, the square from `Homᴸ_X(x,y)` to `X_(x/)`
and from `Homᴸ_S(px,py)` to `S_(px/) ×_S X` is a pullback square.
-/
theorem isPullback_mappingSpaceLeft_sliceUnderComparison {p : X ⟶ S}
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    IsPullback (mappingSpaceLeft.toSliceUnder X x y)
      (mappingSpaceLeft.map X x y p)
      (sliceUnderComparison (p := p) x)
      (mappingSpaceLeftToPullback (p := p) x y) :=
  IsPullback.of_iso_pullback
    (CommSq.mk (mappingSpaceLeft_comp_sliceUnderComparison x y))
    (mappingSpaceLeftIsoPullback x y)
    (by
      change pullback.lift (mappingSpaceLeft.toSliceUnder X x y)
            (mappingSpaceLeft.map X x y p)
            (mappingSpaceLeft_comp_sliceUnderComparison x y) ≫
          pullback.fst (sliceUnderComparison (p := p) x)
            (mappingSpaceLeftToPullback (p := p) x y) =
        mappingSpaceLeft.toSliceUnder X x y
      exact pullback.lift_fst _ _ _)
    (by
      change pullback.lift (mappingSpaceLeft.toSliceUnder X x y)
            (mappingSpaceLeft.map X x y p)
            (mappingSpaceLeft_comp_sliceUnderComparison x y) ≫
          pullback.snd (sliceUnderComparison (p := p) x)
            (mappingSpaceLeftToPullback (p := p) x y) =
        mappingSpaceLeft.map X x y p
      exact pullback.lift_snd _ _ _)

/--
If every under-slice comparison of `p` has the right lifting property against the
Kan–Quillen boundary inclusions, the induced maps on all left mapping spaces are
trivial Kan fibrations, by base change of the comparison maps.
-/
theorem mappingSpaceLeftTrivialFibration_of_forall_rlp_sliceUnderComparison
    {p : X ⟶ S}
    (h : ∀ x : (Δ[0] : SSet.{u}) ⟶ X,
      modelCategoryQuillen.I.rlp (sliceUnderComparison (p := p) x)) :
    MappingSpaceLeftTrivialFibration p :=
  fun a b => MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_mappingSpaceLeft_sliceUnderComparison a b) (h a)

/--
If the under-slice comparison at `x` is a left fibration, the induced map
`Homᴸ_X(x,y) → Homᴸ_S(px,py)` is a left fibration for every vertex `y`.
-/
theorem leftFibration_mappingSpaceLeft_map_of_leftFibration_sliceUnderComparison
    {p : X ⟶ S} (x y : (Δ[0] : SSet.{u}) ⟶ X)
    [LeftFibration (sliceUnderComparison (p := p) x)] :
    LeftFibration (mappingSpaceLeft.map X x y p) :=
  leftFibration_of_isPullback
    (isPullback_mappingSpaceLeft_sliceUnderComparison x y)

end SSet

end
