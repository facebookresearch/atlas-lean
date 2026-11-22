/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.DescentProp412
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Left fibrations and boundary geometry

This file defines left fibrations by their right lifting property against
left horn inclusions, including dimension one, and records stability and
base-change lemmas. It decomposes a simplex boundary as the union of its left
horn and back face, with their actual pullback intersection and pushout gluing.

The square relating naive left mapping spaces to the under-slice comparison
map is a genuine pullback for an arbitrary simplicial map. Its base-change
consequences provide mapping-space lifting properties from the comparison map.
The left-fibration property of that comparison is proved in
`SliceLeftFibration.lean`; boundary transposition and the contractible-fiber
criterion are proved in `ContractibleFiber.lean`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite MorphismProperty
open scoped Simplicial

universe u

namespace SSet

variable {X Y S T E B : SSet.{u}}

/-!
### §1. Left fibrations (sub-goal (1))

Left fibrations in the style of Mathlib's inner fibrations
(`Mathlib.AlgebraicTopology.Quasicategory.InnerFibration`): the
right lifting class of the left horn inclusions `Λ[n, i].ι` for
`i < Fin.last n`, i.e. inner horns together with the left outer
horns `Λ[n, 0]`.
-/

/-- The family of left horn inclusions `Λ[n + 1, i].ι` for
`i < Fin.last (n + 1)` (so `n + 1 ≥ 1` and every left horn,
including `Λ[1, 0]`, occurs). Mirrors
`SSet.innerHornInclusions` with the constraint `0 < i` dropped. -/
inductive leftHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) :
    leftHornInclusions Λ[n + 1, i].ι

/-- Every left horn inclusion `Λ[n, i].ι` with `i < Fin.last n`
is a left horn inclusion in the sense of
`SSet.leftHornInclusions`. -/
lemma horn_ι_mem_leftHornInclusions {n : ℕ} {i : Fin (n + 1)}
    (hi : i < Fin.last n) : leftHornInclusions (horn.{u} n i).ι := by
  obtain _ | k := n
  · grind
  · exact ⟨i, hi⟩

/-- Every inner horn inclusion is a left horn inclusion. -/
lemma innerHornInclusions_le_leftHornInclusions :
    innerHornInclusions.{u} ≤ leftHornInclusions := by
  intro _ _ _ h
  obtain @⟨n, i, -, hn⟩ := h
  exact ⟨i, hn⟩

/-- The left fibrations are the morphisms which have the right
lifting property with respect to left horn inclusions. -/
def leftFibrations : MorphismProperty SSet.{u} := leftHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange,
  IsStableUnderRetracts

/-- A morphism `q` satisfies `[LeftFibration q]` when it has the
right lifting property against every left horn inclusion. Equivalently, it is
an inner fibration which also lifts the left outer horns in every positive
dimension. -/
@[mk_iff]
class LeftFibration {X Y : SSet.{u}} (q : X ⟶ Y) : Prop where
  mem : leftFibrations q

lemma mem_leftFibrations {X Y : SSet.{u}} (q : X ⟶ Y)
    [LeftFibration q] : leftFibrations q :=
  LeftFibration.mem

/-- Every left fibration is an inner fibration, since every
inner horn is a left horn. -/
lemma leftFibrations_le_innerFibrations :
    leftFibrations.{u} ≤ innerFibrations :=
  antitone_rlp innerHornInclusions_le_leftHornInclusions

/-- A left fibration is an inner fibration. -/
theorem LeftFibration.innerFibration {q : X ⟶ Y} [LeftFibration q] :
    InnerFibration q :=
  ⟨leftFibrations_le_innerFibrations _ LeftFibration.mem⟩

instance (priority := 100) {q : X ⟶ Y} [LeftFibration q] :
    InnerFibration q :=
  LeftFibration.innerFibration

/-- A left fibration has the right lifting property against
every left horn inclusion. -/
theorem LeftFibration.hasLiftingProperty_horn {p : X ⟶ S}
    [LeftFibration p] {n : ℕ} {i : Fin (n + 1)} (hi : i < Fin.last n) :
    HasLiftingProperty Λ[n, i].ι p :=
  LeftFibration.mem _ (horn_ι_mem_leftHornInclusions hi)

/-- A map with the right lifting property against every left
horn inclusion is a left fibration. -/
theorem leftFibration_of_hasLiftingProperty_horn {p : X ⟶ S}
    (h : ∀ {n : ℕ} {i : Fin (n + 1)}, i < Fin.last n →
      HasLiftingProperty Λ[n, i].ι p) :
    LeftFibration p := by
  refine ⟨fun _ _ _ hi => ?_⟩
  obtain @⟨n, i, hi⟩ := hi
  exact h hi

/-- A trivial Kan fibration (`modelCategoryQuillen.I.rlp`) is a
left fibration: left horn inclusions are monomorphisms, and
monomorphisms are the left lifting class of `I.rlp`
(`SSet.modelCategoryQuillen.llp_rlp_I`). -/
theorem leftFibration_of_rlp_I {p : X ⟶ S}
    (hp : modelCategoryQuillen.I.rlp p) : LeftFibration p := by
  refine leftFibration_of_hasLiftingProperty_horn (fun {n i} _ => ?_)
  have hmono : monomorphisms SSet.{u} Λ[n, i].ι :=
    monomorphisms.infer_property _
  have hllp : modelCategoryQuillen.I.rlp.llp Λ[n, i].ι :=
    modelCategoryQuillen.llp_rlp_I ▸ hmono
  exact hllp _ hp

/-- Left fibrations are stable under base change: if `p` is the
pullback of a left fibration `q`, then `p` is a left fibration. -/
theorem leftFibration_of_isPullback {p : X ⟶ S} {f : S ⟶ T}
    {q : Y ⟶ T} {g : X ⟶ Y} (sq : IsPullback g p q f)
    [LeftFibration q] : LeftFibration p :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback sq
    LeftFibration.mem⟩

/-- The fiber of a left fibration over a vertex, i.e. the second
projection `pullback q b ⟶ Δ[0]`, is a left fibration; in
particular the fibers of a left fibration have fillers for all
left horns. -/
instance leftFibration_pullback_snd (q : E ⟶ B) [LeftFibration q]
    (b : (Δ[0] : SSet.{u}) ⟶ B) : LeftFibration (pullback.snd q b) :=
  leftFibration_of_isPullback (IsPullback.of_hasPullback q b)

/-- Left horn filling in the fibers of a left fibration: every
left horn in the fiber `pullback q b` over a vertex `b` fills.
This is the fiber half of the classical statement that fibers
of left fibrations are Kan complexes; the missing right outer
horns are not asserted here. -/
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
### §2. The join decomposition of `∂Δ[n + 1]` (sub-goal (4))

Stevenson's decomposition `∂Δⁿ = Δ^{{0}} ⋆ ∂Δ^{{1,…,n}} ∪
Δ^{{1,…,n}}`, in face form: the cone piece `Δ^{{0}} ⋆
∂Δ^{{1,…,n}}` is the left horn `Λ[n, 0]` (the union of the
codimension-one faces opposite vertices `j ≠ 0`, each of which
is a cone on a codimension-two face of the back face), and
`Δ^{{1,…,n}}` is the back face `stdSimplex.face {0}ᶜ`. All
statements are for `∂Δ[n + 1]` so that the back face is a
`Δ[n]`.
-/

/-- **Stevenson's join decomposition, face form**: the boundary
of `Δ[n + 1]` is the union of the left horn `Λ[n + 1, 0]` (the
cone piece `Δ^{{0}} ⋆ ∂Δ^{{1,…,n+1}}`) and the back face
`Δ^{{1,…,n+1}}`. Both sides are suprema of codimension-one
faces (`SSet.boundary_eq_iSup`, `SSet.horn_eq_iSup`); the
boundary's supremum splits off the face opposite `0`. -/
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

/-- The left horn `Λ[n + 1, 0]` is contained in `∂Δ[n + 1]`. -/
lemma horn_zero_le_boundary (n : ℕ) :
    Λ[n + 1, (0 : Fin (n + 2))] ≤ boundary.{u} (n + 1) := by
  rw [boundary_eq_horn_zero_sup_face]
  exact le_sup_left

/-- The intersection of the two pieces of Stevenson's
decomposition: the cone piece meets the back face in the union
of the codimension-two faces `Δ^{{0, j}ᶜ}` for `j ≠ 0`, written
here as `face ({j}ᶜ ⊓ {0}ᶜ)`. Under the back-face
identification this is `∂Δ^{{1,…,n+1}}` (see
`SSet.preimage_horn_zero_inf_face_delta_zero`). -/
theorem horn_zero_inf_face_eq_iSup (n : ℕ) :
    Λ[n + 1, (0 : Fin (n + 2))] ⊓
        stdSimplex.face {(0 : Fin (n + 2))}ᶜ =
      ⨆ (j : ({(0 : Fin (n + 2))}ᶜ : Set (Fin (n + 2)))),
        stdSimplex.face ({j.1}ᶜ ⊓ {(0 : Fin (n + 2))}ᶜ) := by
  rw [horn_eq_iSup, Subfunctor.iSup_min]
  exact iSup_congr fun j => stdSimplex.face_inter_face _ _

/-- Pulling the left horn `Λ[n + 1, 0]` back along the back
face inclusion `δ₀ : Δ[n] ⟶ Δ[n + 1]` gives the boundary
`∂Δ[n]`: a simplex `f` of `Δ[n]` lands in the horn after `δ₀`
iff `range (δ₀ ∘ f) ∪ {0}` is not everything, iff `f` is not
surjective, since `δ₀` is `Fin.succAbove 0` with range `{0}ᶜ`. -/
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

/-- Pulling the back face `Δ^{{1,…,n+1}}` back along its own
inclusion `δ₀ : Δ[n] ⟶ Δ[n + 1]` gives all of `Δ[n]`: every
simplex in the image of `δ₀` has all vertices in `{0}ᶜ`, since
`δ₀ = Fin.succAbove 0` never takes the value `0`. -/
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

/-- The intersection of the two pieces of Stevenson's
decomposition, pulled back along the back face inclusion `δ₀`,
is `∂Δ[n]` — the boundary of the back face `Δ^{{1,…,n+1}} ≅
Δ[n]`. This is the overlap term of the transposed square in
Stevenson's Step 3. -/
theorem preimage_horn_zero_inf_face_delta_zero (n : ℕ) :
    (Λ[n + 1, (0 : Fin (n + 2))] ⊓
        stdSimplex.face {(0 : Fin (n + 2))}ᶜ).preimage
        (stdSimplex.δ (0 : Fin (n + 2))) =
      boundary.{u} n := by
  rw [Subcomplex.preimage_min, preimage_horn_zero_delta_zero,
    preimage_face_zero_delta_zero, inf_top_eq]

/-- **`∂Δ[n + 1]` is the pushout of its two Stevenson
pieces**: the square of subcomplex inclusions from the
intersection `Λ[n + 1, 0] ⊓ Δ^{{1,…,n+1}}` to the left horn and
the back face, completed by their inclusions into `∂Δ[n + 1]`,
is a pushout. This is `SSet.Subcomplex.BicartSq.isPushout` for
the bicartesian square of subcomplexes given by
`SSet.boundary_eq_horn_zero_sup_face`. -/
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

/-- **Gluing maps out of `∂Δ[n + 1]` along Stevenson's
decomposition**: maps out of the cone piece `Λ[n + 1, 0]` and
out of the back face `Δ^{{1,…,n+1}}` which agree on their
intersection glue uniquely to a map out of `∂Δ[n + 1]`. -/
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

/-- The `0`-th vertex of a map out of `∂Δ[n + 1]`, as a map
`Δ[0] ⟶ X`: Stevenson's `x = u(0)` in Step 3. It is the
constant vertex map at the image of the `0`-simplex of
`∂Δ[n + 1]` classified by the vertex `0` of `Δ[n + 1]` (which
lies in the boundary since `n + 1 ≥ 1`). -/
def boundaryVertexZero {n : ℕ} {X : SSet.{u}}
    (u : ((boundary (n + 1) : (Δ[n + 1] : SSet.{u}).Subcomplex) :
      SSet.{u}) ⟶ X) :
    (Δ[0] : SSet.{u}) ⟶ X :=
  SSet.const (u.app (op ⦋0⦌)
    ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), by
      rw [boundary_obj_eq_univ 0 (n + 1) (Nat.zero_lt_succ n)]
      exact Set.mem_univ _⟩)

/-!
### §3. The fiber identification (sub-goal (2))

The fiber of `SSet.sliceUnderComparison` over a vertex `y` is
the naive mapping-space map `SSet.mappingSpaceLeft.map X x y p`:
precisely, `SSet.mappingSpaceLeft X x y` is the pullback of the
comparison map along the canonical map
`SSet.mappingSpaceLeftToPullback` from the target mapping space
to `S_{x/} ×_S X` (the point `y` on the `X`-factor).
-/

/-- Simplices of the form `b.app n s` for `b : Δ[0] ⟶ Z` and
`s` an `n`-simplex of `Δ[0]` are all equal to the constant
simplex at `b`: maps into `Δ[0]` are unique
(`SSet.toDeltaZero_eq`). -/
lemma toDeltaZero_comp_app {Z M : SSet.{u}}
    (b : (Δ[0] : SSet.{u}) ⟶ Z) {n : SimplexCategoryᵒᵖ}
    (t : M.obj n) :
    b.app n ((toDeltaZero M).app n t) =
      SSet.yonedaEquiv (toDeltaZero (SSet.stdSimplex.obj n.unop) ≫ b) := by
  rw [← toDeltaZero_eq
    (SSet.yonedaEquiv.symm ((toDeltaZero M).app n t)),
    yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- The under-slice projection of a left mapping space simplex
is constantly the target vertex, as a map: the composite
`Homᴸ_Z(a, b) → Z_{a/} → Z` is the constant map at `b`. This is
the map-level form of
`SSet.mappingSpaceLeft.proj_toSliceUnder_apply`. -/
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

/-- The canonical map from the target naive mapping space
`Homᴸ_S(x ≫ p, y ≫ p)` to the pullback `S_{x/} ×_S X`: first
component the inclusion into the under-slice, second component
the constant map at `y`. The fiber of
`SSet.sliceUnderComparison` over the vertex `y` is taken along
this map. -/
noncomputable def mappingSpaceLeftToPullback {p : X ⟶ S}
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    mappingSpaceLeft S (x ≫ p) (y ≫ p) ⟶
      pullback (sliceUnder.proj S (x ≫ p)) p :=
  pullback.lift (mappingSpaceLeft.toSliceUnder S (x ≫ p) (y ≫ p))
    (toDeltaZero (mappingSpaceLeft S (x ≫ p) (y ≫ p)) ≫ y)
    (by rw [mappingSpaceLeft_toSliceUnder_proj, Category.assoc])

@[reassoc (attr := simp)]
theorem mappingSpaceLeftToPullback_fst {p : X ⟶ S}
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    mappingSpaceLeftToPullback (p := p) x y ≫
        pullback.fst (sliceUnder.proj S (x ≫ p)) p =
      mappingSpaceLeft.toSliceUnder S (x ≫ p) (y ≫ p) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem mappingSpaceLeftToPullback_snd {p : X ⟶ S}
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    mappingSpaceLeftToPullback (p := p) x y ≫
        pullback.snd (sliceUnder.proj S (x ≫ p)) p =
      toDeltaZero (mappingSpaceLeft S (x ≫ p) (y ≫ p)) ≫ y :=
  pullback.lift_snd _ _ _

/-- The fiber square commutes: mapping-space functoriality is
compatible with the slice comparison map. -/
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

lemma pullback_snd_app_sliceUnderComparison_app {p : X ⟶ S}
    (x : (Δ[0] : SSet.{u}) ⟶ X) {n : SimplexCategoryᵒᵖ}
    (w : (sliceUnder X x).obj n) :
    (pullback.snd (sliceUnder.proj S (x ≫ p)) p).app n
        ((sliceUnderComparison (p := p) x).app n w) =
      (sliceUnder.proj X x).app n w :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (sliceUnderComparison_snd (p := p) x) n) w

lemma pullback_fst_app_sliceUnderComparison_app {p : X ⟶ S}
    (x : (Δ[0] : SSet.{u}) ⟶ X) {n : SimplexCategoryᵒᵖ}
    (w : (sliceUnder X x).obj n) :
    (pullback.fst (sliceUnder.proj S (x ≫ p)) p).app n
        ((sliceUnderComparison (p := p) x).app n w) =
      (sliceUnder.map X x p).app n w :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (sliceUnderComparison_fst (p := p) x) n) w

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

lemma pullback_fst_app_mappingSpaceLeftToPullback_app
    {p : X ⟶ S} (x y : (Δ[0] : SSet.{u}) ⟶ X)
    {n : SimplexCategoryᵒᵖ}
    (w : (mappingSpaceLeft S (x ≫ p) (y ≫ p)).obj n) :
    (pullback.fst (sliceUnder.proj S (x ≫ p)) p).app n
        ((mappingSpaceLeftToPullback (p := p) x y).app n w) =
      (mappingSpaceLeft.toSliceUnder S (x ≫ p) (y ≫ p)).app n w :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (mappingSpaceLeftToPullback_fst (p := p) x y) n) w

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

/-- The comparison map from the naive mapping space to the
pullback of the slice comparison map along
`SSet.mappingSpaceLeftToPullback` is an isomorphism: an
`n`-simplex of the pullback is a join map `Δ[0] ⋆ Δ[n] ⟶ X`
restricting to `x` on the left (the under-slice condition) and
to the constant simplex at `y` on the right (read off the
second pullback projection), together with its postcomposition
along `p` (read off the first) — exactly an `n`-simplex of
`SSet.mappingSpaceLeft X x y`. -/
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

/-- **The fiber identification (sub-goal (2))**: the square
```
Homᴸ_X(x, y) ──────────→ X_{x/}
     │                      │  sliceUnderComparison
     │ map p                ↓
Homᴸ_S(xp, yp) ───────→ S_{x/} ×_S X
```
is a pullback square. In Stevenson's notation: the fiber of
`X_{x/} → S_{x/} ×_S X` over `y` is the map
`X_{x/} ×_X {y} → S_{x/} ×_S {y}` on naive mapping spaces. -/
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

/-- If every slice comparison map of `p` is a trivial Kan
fibration, then `p` induces trivial Kan fibrations on all
naive (left) mapping spaces: base change along the fiber
square of `SSet.isPullback_mappingSpaceLeft_sliceUnderComparison`.
This is the trivial-fibration case of Stevenson's Lemma 2.17
(the direction used to see that trivial Kan fibrations are
fully faithful). -/
theorem mappingSpaceLeftTrivialFibration_of_forall_rlp_sliceUnderComparison
    {p : X ⟶ S}
    (h : ∀ x : (Δ[0] : SSet.{u}) ⟶ X,
      modelCategoryQuillen.I.rlp (sliceUnderComparison (p := p) x)) :
    MappingSpaceLeftTrivialFibration p :=
  fun a b => MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_mappingSpaceLeft_sliceUnderComparison a b) (h a)

/-- If the slice comparison map at `x` is a left fibration,
then every induced naive mapping-space map out of `x` is a
left fibration: base change along the fiber square. -/
theorem leftFibration_mappingSpaceLeft_map_of_leftFibration_sliceUnderComparison
    {p : X ⟶ S} (x y : (Δ[0] : SSet.{u}) ⟶ X)
    [LeftFibration (sliceUnderComparison (p := p) x)] :
    LeftFibration (mappingSpaceLeft.map X x y p) :=
  leftFibration_of_isPullback
    (isPullback_mappingSpaceLeft_sliceUnderComparison x y)

end SSet

end
