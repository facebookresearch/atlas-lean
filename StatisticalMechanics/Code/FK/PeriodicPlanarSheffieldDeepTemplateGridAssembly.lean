/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldCommonArray










open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicPlaneEmbedding.exists_uniformTemplate_deepGridPreference_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
        atTop (nhds 1)) :
    ∃ radius : Nat → Nat, ∀
      (width height margin : Nat → Nat)
      (hwidth : ∀ n, 0 < width n)
      (base : Nat → Site 2)
      (vertical horizontal : (n : Nat) →
        PreferenceGridVertex (width n) (height n) → Bool)
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
        margin n ≤ v.1.val → v.1.val + margin n < width n →
        margin n ≤ v.2.val → v.2.val + margin n < height n →
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
      (∀ n v, v.2.val ≤ margin n → vertical n v = true) →
      (∀ n v, height n ≤ v.2.val + margin n →
        vertical n v = false) →
      (∀ n v, v.1.val ≤ margin n → horizontal n v = true) →
      (∀ n v, width n ≤ v.1.val + margin n →
        horizontal n v = false) →
      (∀ n v, vertical n v = true →
        top n v ≤ bottom n v + epsilon n) →
      (∀ n v, vertical n v = false →
        bottom n v ≤ top n v + epsilon n) →
      (∀ n v, horizontal n v = true →
        right n v ≤ left n v + epsilon n) →
      (∀ n v, horizontal n v = false →
        left n v ≤ right n v + epsilon n) →
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
  intro width height margin hwidth base vertical horizontal a b c d epsilon
    bottom top left right hepsilon hepsilon0 hsource hconnector
    hbottomScore htopScore hleftScore hrightScore
    hVbottom hVtop hHleft hHright hVtrue hVfalse hHtrue hHfalse
  have hwitness (n : Nat) := exists_deep_common_preference_grid_witness
    (hwidth n) (vertical n) (horizontal n)
      (hVbottom n) (hVtop n) (hHleft n) (hHright n)
  choose x xVertical xHorizontal hxV hxH hxVadj hxVfalse
    hxHadj hxHfalse hxLeft hxRight hxBottom hxTop using hwitness
  choose ijV hijV using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxVadj n)
  choose ijH hijH using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxHadj n)
  let source : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Finset V := fun n v =>
    (template n).image (P.shift (base n + preferenceGridSite v))
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
    exact hconnector n (x n) (hxLeft n) (hxRight n)
      (hxBottom n) (hxTop n)
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
  have hbranch (n : Nat) :
      (1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))) ≤
            bottom n (x n) + epsilon n ∧
        bottom n (x n) *
            (mu.real (P.setHitsInfinite
                (source n (xVertical n) : Set V)) * bottom n (x n) -
              Mv n - epsilon n) - Mv n ≤
          mu.real (E.verticalCrossingEvent
            (a n) (b n) (c n) (d n))) ∨
      (1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))) ≤
            left n (x n) + epsilon n ∧
        left n (x n) *
            (mu.real (P.setHitsInfinite
                (source n (xHorizontal n) : Set V)) * left n (x n) -
              Mh n - epsilon n) - Mh n ≤
          mu.real (E.horizontalCrossingEvent
            (a n) (b n) (c n) (d n))) := by
    have hBT := hVtrue n (x n) (hxV n)
    have hLR := hHtrue n (x n) (hxH n)
    rw [hbottomScore n (x n), htopScore n (x n)] at hBT
    rw [hleftScore n (x n), hrightScore n (x n)] at hLR
    have hpref := E.preference_max_bottom_left_add_epsilon_ge_fourthRoot
      mu hFKG (a n) (b n) (c n) (d n)
      (source n (x n) : Set V) (epsilon n) (hepsilon0 n)
      (by simpa only [source] using hsource n (x n))
      (by simpa only [source] using hBT)
      (by simpa only [source] using hLR)
    have hpref' :
        1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite
              (source n (x n) : Set V)))) ≤
          max (bottom n (x n)) (left n (x n)) + epsilon n := by
      calc
        _ ≤ max
            (mu.real (E.rectSideConnectionEvent
              (a n) (b n) (c n) (d n) (source n (x n) : Set V)
              (E.rectBottomBoundaryVertices
                (a n) (b n) (c n) (d n))))
            (mu.real (E.rectSideConnectionEvent
              (a n) (b n) (c n) (d n) (source n (x n) : Set V)
              (E.rectLeftBoundaryVertices
                (a n) (b n) (c n) (d n)))) + epsilon n := by
                  simpa using hpref
        _ = max (bottom n (x n)) (left n (x n)) + epsilon n := by
          rw [hbottomScore n (x n), hleftScore n (x n)]
    by_cases hLB : left n (x n) ≤ bottom n (x n)
    · left
      have hroot :
          1 - Real.sqrt (Real.sqrt
              (1 - mu.real (P.setHitsInfinite
              (source n (x n) : Set V)))) ≤
            bottom n (x n) + epsilon n := by
        simpa [max_eq_left hLB] using hpref'
      have hOpp := hVfalse n (xVertical n) (hxVfalse n)
      rw [hbottomScore n (xVertical n),
        htopScore n (xVertical n)] at hOpp
      have htransfer := E.verticalCrossing_ge_approxPreferredSide_transfer
        mu hFKG (a n) (b n) (c n) (d n)
        (source n (x n)) (source n (xVertical n)) (epsilon n)
        (by simpa only [source] using hOpp)
      rw [← hbottomScore n (x n)] at htransfer
      simpa only [Mv] using And.intro hroot htransfer
    · right
      have hBL : bottom n (x n) ≤ left n (x n) := le_of_not_ge hLB
      have hroot :
          1 - Real.sqrt (Real.sqrt
              (1 - mu.real (P.setHitsInfinite
              (source n (x n) : Set V)))) ≤
            left n (x n) + epsilon n := by
        simpa [max_eq_right hBL] using hpref'
      have hOpp := hHfalse n (xHorizontal n) (hxHfalse n)
      rw [hleftScore n (xHorizontal n),
        hrightScore n (xHorizontal n)] at hOpp
      have htransfer := E.horizontalCrossing_ge_approxPreferredSide_transfer
        mu hFKG (a n) (b n) (c n) (d n)
        (source n (x n)) (source n (xHorizontal n)) (epsilon n)
        (by simpa only [source] using hOpp)
      rw [← hleftScore n (x n)] at htransfer
      simpa only [Mh] using And.intro hroot htransfer
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
    · simpa [A, root, hv] using
        ((hbranch n).resolve_left hv).1
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
      have hb := (hbranch n).resolve_left hv
      simpa [A, Hh, Ch, hv] using hb.2
  simpa [Cv, Ch] using
    crossing_max_tendsto_one_of_approxPreferredSide_root_branches
      root A Hv Hh Mv Mh epsilon Cv Ch hroot hrootA hAupper
      hHv hHh hMv hMh hepsilon hcrossingBranch
      (fun _ => measureReal_le_one) (fun _ => measureReal_le_one)

end StatMech.FK.PeriodicPlanar
