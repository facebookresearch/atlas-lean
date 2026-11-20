/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldApproximatePreference
import Code.FK.PeriodicPlanarSheffieldTemplateMerge











open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}





theorem PeriodicPlaneEmbedding.exists_uniformTemplate_approxPreference_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
        atTop (nhds 1)) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n)
      (base : Nat → Site 2)
      (a b c d epsilon : Nat → Real)
      (bottom top left right : (n : Nat) →
        PreferenceGridVertex (width n) (height n) → Real),
      Tendsto epsilon atTop (nhds 0) →
      (∀ n, 0 ≤ epsilon n) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n v, bottom n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, top n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, left n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, right n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n (i : Fin (width n + 1)),
        top n (i, 0) ≤ bottom n (i, 0) + epsilon n) →
      (∀ n (i : Fin (width n + 1)),
        bottom n (i, Fin.last (height n)) ≤
          top n (i, Fin.last (height n)) + epsilon n) →
      (∀ n (j : Fin (height n + 1)),
        right n (0, j) ≤ left n (0, j) + epsilon n) →
      (∀ n (j : Fin (height n + 1)),
        left n (Fin.last (width n), j) ≤
          right n (Fin.last (width n), j) + epsilon n) →
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
        (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))))
        atTop (nhds 1) := by
  classical
  let neighbor : Nat → (Fin 3 × Fin 3) → Finset V := fun n ij =>
    (template n).image (P.shift (preferenceKingOffset ij))
  obtain ⟨radius, _hradius, hmerge⟩ :=
    E.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      mu hTI hunique template neighbor
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight base a b c d epsilon
    bottom top left right hepsilon hepsilon0 hsource hrect
    hbottomScore htopScore hleftScore hrightScore
    hbottom htop hleft hright
  let source : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Finset V := fun n v =>
    (template n).image (P.shift (base n + preferenceGridSite v))
  have hfiniteBranch (n : Nat) :=
    E.exists_approxPreferredSide_crossing_branch mu hFKG
      (a n) (b n) (c n) (d n) (hwidth n) (hheight n)
      (epsilon n) (hepsilon0 n) (source n)
      (bottom n) (top n) (left n) (right n)
      (by simpa only [source] using hsource n)
      (hbottomScore n) (htopScore n) (hleftScore n) (hrightScore n)
      (hbottom n) (htop n) (hleft n) (hright n)
  choose x xVertical xHorizontal hxV hxH hbranch using hfiniteBranch
  choose ijV hijV using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxV n)
  choose ijH hijH using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxH n)
  let z : Nat → Site 2 := fun n => base n + preferenceGridSite (x n)
  have hzV (n : Nat) :
      z n + preferenceKingOffset (ijV n) =
        base n + preferenceGridSite (xVertical n) := by
    dsimp only [z]
    rw [hijV n]
    simp only [add_assoc]
  have hzH (n : Nat) :
      z n + preferenceKingOffset (ijH n) =
        base n + preferenceGridSite (xHorizontal n) := by
    dsimp only [z]
    rw [hijH n]
    simp only [add_assoc]
  have hneighbor (n : Nat) (ij : Fin 3 × Fin 3) :
      (neighbor n ij).image (P.shift (z n)) =
        (template n).image
          (P.shift (z n + preferenceKingOffset ij)) := by
    simp only [neighbor, Finset.image_image]
    apply Finset.image_congr
    intro u hu
    simpa [add_comm] using
      (P.shift_add (preferenceKingOffset ij) (z n) u).symm
  have hrectZ (n : Nat) :
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
          E.rectVertices (a n) (b n) (c n) (d n) := by
    exact hrect n (x n)
  have hMv0 := hmerge z ijV a b c d hrectZ
  have hMh0 := hmerge z ijH a b c d hrectZ
  let Mv : Nat → Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      (source n (x n)) (source n (xVertical n)))
  let Mh : Nat → Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      (source n (x n)) (source n (xHorizontal n)))
  have hMv : Tendsto Mv atTop (nhds 0) := by
    simpa only [Mv, source, z, hneighbor, hzV] using hMv0
  have hMh : Tendsto Mh atTop (nhds 0) := by
    simpa only [Mh, source, z, hneighbor, hzH] using hMh0
  let verticalBranch : Nat → Prop := fun n =>
    1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))) ≤
          bottom n (x n) + epsilon n ∧
      bottom n (x n) *
          (mu.real (P.setHitsInfinite
              (source n (xVertical n) : Set V)) * bottom n (x n) -
            Mv n - epsilon n) - Mv n ≤
        mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))
  let A : Nat → Real := fun n =>
    if verticalBranch n then bottom n (x n) else left n (x n)
  let Hv : Nat → Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xVertical n) : Set V))
  let Hh : Nat → Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xHorizontal n) : Set V))
  let Cv : Nat → Real := fun n =>
    mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))
  let Ch : Nat → Real := fun n =>
    mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))
  let root : Nat → Real := fun n =>
    1 - Real.sqrt (Real.sqrt
      (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V))))
  have htranslatedHit (y : (n : Nat) →
      PreferenceGridVertex (width n) (height n)) : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (source n (y n) : Set V)))
      atTop (nhds 1) := by
    apply htemplateHit.congr'
    filter_upwards with n
    have hset : ((source n (y n) : Finset V) : Set V) =
        P.shift (base n + preferenceGridSite (y n)) ''
          (template n : Set V) := by
      ext v
      simp [source]
    rw [hset, P.setHitsInfinite_translate_measureReal_eq mu hTI]
  have hroot : Tendsto root atTop (nhds 1) := by
    have hhit := htranslatedHit x
    have hmiss : Tendsto (fun n =>
        1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hhit
    simpa [root] using tendsto_const_nhds.sub hmiss.sqrt.sqrt
  have hHv : Tendsto Hv atTop (nhds 1) := by
    simpa [Hv] using htranslatedHit xVertical
  have hHh : Tendsto Hh atTop (nhds 1) := by
    simpa [Hh] using htranslatedHit xHorizontal
  have hrootA (n : Nat) : root n ≤ A n + epsilon n := by
    by_cases hv : verticalBranch n
    · simpa [A, root, hv] using hv.1
    · have hh := (hbranch n).resolve_left hv
      simpa [A, root, hv] using hh.1
  have hAupper (n : Nat) : A n ≤ 1 := by
    by_cases hv : verticalBranch n
    · simp only [A, if_pos hv]
      rw [hbottomScore n (x n)]
      exact measureReal_le_one
    · simp only [A, if_neg hv]
      rw [hleftScore n (x n)]
      exact measureReal_le_one
  have hcrossingBranch (n : Nat) :
      A n * (Hv n * A n - Mv n - epsilon n) - Mv n ≤ Cv n ∨
      A n * (Hh n * A n - Mh n - epsilon n) - Mh n ≤ Ch n := by
    by_cases hv : verticalBranch n
    · left
      simpa [A, Hv, Cv, hv] using hv.2
    · right
      have hh := (hbranch n).resolve_left hv
      simpa [A, Hh, Mh, Ch, hv] using hh.2
  simpa [Cv, Ch] using
    crossing_max_tendsto_one_of_approxPreferredSide_root_branches
      root A Hv Hh Mv Mh epsilon Cv Ch hroot hrootA hAupper
      hHv hHh hMv hMh hepsilon hcrossingBranch
      (fun _ => measureReal_le_one) (fun _ => measureReal_le_one)

end StatMech.FK.PeriodicPlanar
