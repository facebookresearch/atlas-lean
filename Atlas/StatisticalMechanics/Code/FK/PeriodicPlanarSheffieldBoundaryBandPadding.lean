/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldDeepTemplateGridAssembly
import Code.FK.PeriodicPlanarSheffieldOrientedBoundary









open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



theorem PeriodicPlaneEmbedding.exists_common_leftBoundaryExhaustion_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (source : ι → Finset V)
    (hinside : ∀ i, (source i : Set V) ⊆ E.rightHalfPlaneVertices r)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat,
      ∀ i,
        (source i : Set V) ⊆ E.leftBoundaryExhaustionVertices r radius ∧
        mu.real (P.infiniteSetConnectionWithin
            (E.rightHalfPlaneVertices r) (source i : Set V)
            (E.rightHalfPlaneBoundaryVertices r)) - epsilon <
          mu.real (E.leftBoundaryExhaustionEvent r
            (source i : Set V) radius) := by
  choose localRadius hlocal using fun i =>
    E.exists_leftBoundaryExhaustion_measureReal_gt mu r
      (source i).finite_toSet (hinside i) hepsilon
  let radius : Nat := ∑ i : ι, localRadius i
  refine ⟨radius, ?_⟩
  intro i
  have hle : localRadius i ≤ radius := by
    dsimp only [radius]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  constructor
  · exact fun v hv => E.leftBoundaryExhaustionVertices_mono r hle
      ((hlocal i).1 hv)
  · exact (hlocal i).2.trans_le (measureReal_mono
      (E.leftBoundaryExhaustionEvent_mono r (source i : Set V) hle))




theorem PeriodicPlaneEmbedding.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (shift : ι → Site 2)
    (hinside : ∀ i,
      P.shift (shift i) '' (S : Set V) ⊆ E.rightHalfPlaneVertices r)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat,
      ∀ i,
        P.shift (shift i) '' (S : Set V) ⊆
            E.leftBoundaryExhaustionVertices r radius ∧
        (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
          mu.real (E.leftBoundaryExhaustionEvent r
            (P.shift (shift i) '' (S : Set V)) radius) := by
  obtain ⟨boxRadius, hSbox⟩ := P.finite_subset_orbitBox S
  obtain ⟨outsideBase, houtsideBase⟩ :=
    E.exists_shift_orbitBox_subset_leftComplement boxRadius r
  let source : ι → Finset V := fun i => S.image (P.shift (shift i))
  have hsourceSet (i : ι) : (source i : Set V) =
      P.shift (shift i) '' (S : Set V) := by
    ext v
    simp [source]
  have houtside (i : ι) :
      P.shift (outsideBase - shift i) '' (source i : Set V) ⊆
        (E.rightHalfPlaneVertices r)ᶜ := by
    rw [hsourceSet]
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have hshift :
        P.shift (outsideBase - shift i) (P.shift (shift i) v) =
          P.shift outsideBase v := by
      rw [← P.shift_add]
      simp
    rw [hshift]
    exact houtsideBase v (hSbox v hv)
  obtain ⟨radius, hradius⟩ :=
    E.exists_common_leftBoundaryExhaustion_measureReal_gt
      mu r source (fun i => by simpa only [hsourceSet] using hinside i)
        hepsilon
  refine ⟨radius, ?_⟩
  intro i
  have hhalf := E.infiniteBoundaryConnection_measureReal_ge_sq_of_translate
    mu hFKG hTI hunique r (source i : Set V)
      (outsideBase - shift i)
      (by simpa only [hsourceSet] using hinside i) (houtside i)
  have hmass : mu.real (P.setHitsInfinite (source i : Set V)) =
      mu.real (P.setHitsInfinite (S : Set V)) := by
    rw [hsourceSet, P.setHitsInfinite_translate_measureReal_eq mu hTI]
  rw [hmass] at hhalf
  constructor
  · simpa only [hsourceSet] using (hradius i).1
  · rw [← hsourceSet i]
    linarith [(hradius i).2]


theorem PeriodicPlaneEmbedding.exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (shift : ι → Site 2)
    (hinside : ∀ i, P.shift (shift i) '' (S : Set V) ⊆
      {v | E.vertexCoord v 0 ≤ -r})
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ i,
      P.shift (shift i) '' (S : Set V) ⊆
          E.rectVertices (-(r + radius)) (-r)
            (-(radius : Real)) radius ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent
          (-(r + radius)) (-r) (-(radius : Real)) radius
          (P.shift (shift i) '' (S : Set V))
          (E.rectRightBoundaryVertices
            (-(r + radius)) (-r) (-(radius : Real)) radius)) := by
  have huniqueNeg :
      mu {omega | P.axisNeg.HasUniqueInfiniteCluster omega} = 1 := by
    simpa [PeriodicGraph.axisNeg] using hunique
  let shiftNeg : ι → Site 2 := fun i => siteNeg (shift i)
  have hinsideNeg (i : ι) :
      P.axisNeg.shift (shiftNeg i) '' (S : Set V) ⊆
        E.axisNeg.rightHalfPlaneVertices r := by
    intro x hx
    have hx' : x ∈ P.shift (shift i) '' (S : Set V) := by
      simpa [shiftNeg, PeriodicGraph.axisNeg] using hx
    have hcoord := hinside i hx'
    change E.vertexCoord x 0 ≤ -r at hcoord
    change r ≤ E.axisNeg.vertexCoord x 0
    rw [E.axisNeg_vertexCoord]
    linarith
  obtain ⟨radius, hradius⟩ :=
    E.axisNeg.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt
      mu hFKG (P.axisNeg_isTranslationInvariant mu hTI) huniqueNeg
      r S shiftNeg hinsideNeg hepsilon
  refine ⟨radius, ?_⟩
  intro i
  have hhit : P.axisNeg.setHitsInfinite (S : Set V) =
      P.setHitsInfinite (S : Set V) := rfl
  obtain ⟨hsub, hprob⟩ := hradius i
  constructor
  · intro x hx
    have hx' : x ∈ P.axisNeg.shift (shiftNeg i) '' (S : Set V) := by
      simpa [shiftNeg, PeriodicGraph.axisNeg] using hx
    have hmem := hsub hx'
    change x ∈ E.axisNeg.rectVertices r (r + radius)
      (-(radius : Real)) radius at hmem
    rw [E.axisNeg_rectVertices] at hmem
    simpa only [neg_neg] using hmem
  · have hshiftSet :
        P.axisNeg.shift (shiftNeg i) '' (S : Set V) =
          P.shift (shift i) '' (S : Set V) := by
      ext x
      simp [shiftNeg, PeriodicGraph.axisNeg]
    change (mu.real (P.axisNeg.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
      mu.real (E.axisNeg.rectSideConnectionEvent r (r + radius)
        (-(radius : Real)) radius
        (P.axisNeg.shift (shiftNeg i) '' (S : Set V))
        (E.axisNeg.rectLeftBoundaryVertices r (r + radius)
          (-(radius : Real)) radius)) at hprob
    rw [hhit, hshiftSet] at hprob
    rw [E.axisNeg_leftBoundaryEvent] at hprob
    simpa only [neg_neg] using hprob


theorem PeriodicPlaneEmbedding.exists_translatedFamily_bottomBoundaryExhaustion_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (shift : ι → Site 2)
    (hinside : ∀ i, P.shift (shift i) '' (S : Set V) ⊆
      {v | r ≤ E.vertexCoord v 1})
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ i,
      P.shift (shift i) '' (S : Set V) ⊆
          E.rectVertices (-(radius : Real)) radius r (r + radius) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent
          (-(radius : Real)) radius r (r + radius)
          (P.shift (shift i) '' (S : Set V))
          (E.rectBottomBoundaryVertices
            (-(radius : Real)) radius r (r + radius))) := by
  have huniqueSwap :
      mu {omega | P.axisSwap.HasUniqueInfiniteCluster omega} = 1 := by
    simpa [PeriodicGraph.axisSwap] using hunique
  let shiftSwap : ι → Site 2 := fun i => siteAxisSwap (shift i)
  have hinsideSwap (i : ι) :
      P.axisSwap.shift (shiftSwap i) '' (S : Set V) ⊆
        E.axisSwap.rightHalfPlaneVertices r := by
    intro x hx
    have hx' : x ∈ P.shift (shift i) '' (S : Set V) := by
      simpa [shiftSwap, PeriodicGraph.axisSwap, siteAxisSwap_swap] using hx
    have hcoord := hinside i hx'
    change r ≤ E.axisSwap.vertexCoord x 0
    simpa using hcoord
  obtain ⟨radius, hradius⟩ :=
    E.axisSwap.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt
      mu hFKG (P.axisSwap_isTranslationInvariant mu hTI) huniqueSwap
      r S shiftSwap hinsideSwap hepsilon
  refine ⟨radius, ?_⟩
  intro i
  have hhit : P.axisSwap.setHitsInfinite (S : Set V) =
      P.setHitsInfinite (S : Set V) := rfl
  obtain ⟨hsub, hprob⟩ := hradius i
  constructor
  · intro x hx
    have hx' : x ∈ P.axisSwap.shift (shiftSwap i) '' (S : Set V) := by
      simpa [shiftSwap, PeriodicGraph.axisSwap, siteAxisSwap_swap] using hx
    have hmem := hsub hx'
    change x ∈ E.axisSwap.rectVertices r (r + radius)
      (-(radius : Real)) radius at hmem
    rw [E.axisSwap_rectVertices] at hmem
    exact hmem
  · have hshiftSet :
        P.axisSwap.shift (shiftSwap i) '' (S : Set V) =
          P.shift (shift i) '' (S : Set V) := by
      ext x
      simp [shiftSwap, PeriodicGraph.axisSwap, siteAxisSwap_swap]
    change (mu.real (P.axisSwap.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
      mu.real (E.axisSwap.rectSideConnectionEvent r (r + radius)
        (-(radius : Real)) radius
        (P.axisSwap.shift (shiftSwap i) '' (S : Set V))
        (E.axisSwap.rectLeftBoundaryVertices r (r + radius)
          (-(radius : Real)) radius)) at hprob
    rw [hhit, hshiftSet] at hprob
    rw [E.axisSwap_leftBoundaryEvent] at hprob
    exact hprob


theorem PeriodicPlaneEmbedding.exists_translatedFamily_topBoundaryExhaustion_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (shift : ι → Site 2)
    (hinside : ∀ i, P.shift (shift i) '' (S : Set V) ⊆
      {v | E.vertexCoord v 1 ≤ -r})
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ i,
      P.shift (shift i) '' (S : Set V) ⊆
          E.rectVertices (-(radius : Real)) radius
            (-(r + radius)) (-r) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent
          (-(radius : Real)) radius (-(r + radius)) (-r)
          (P.shift (shift i) '' (S : Set V))
          (E.rectTopBoundaryVertices
            (-(radius : Real)) radius (-(r + radius)) (-r))) := by
  have huniqueSwap :
      mu {omega | P.axisSwap.HasUniqueInfiniteCluster omega} = 1 := by
    simpa [PeriodicGraph.axisSwap] using hunique
  let shiftSwap : ι → Site 2 := fun i => siteAxisSwap (shift i)
  have hinsideSwap (i : ι) :
      P.axisSwap.shift (shiftSwap i) '' (S : Set V) ⊆
        {v | E.axisSwap.vertexCoord v 0 ≤ -r} := by
    intro x hx
    have hx' : x ∈ P.shift (shift i) '' (S : Set V) := by
      simpa [shiftSwap, PeriodicGraph.axisSwap, siteAxisSwap_swap] using hx
    have hcoord := hinside i hx'
    change E.axisSwap.vertexCoord x 0 ≤ -r
    simpa using hcoord
  obtain ⟨radius, hradius⟩ :=
    E.axisSwap.exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt
      mu hFKG (P.axisSwap_isTranslationInvariant mu hTI) huniqueSwap
      r S shiftSwap hinsideSwap hepsilon
  refine ⟨radius, ?_⟩
  intro i
  have hhit : P.axisSwap.setHitsInfinite (S : Set V) =
      P.setHitsInfinite (S : Set V) := rfl
  obtain ⟨hsub, hprob⟩ := hradius i
  constructor
  · intro x hx
    have hx' : x ∈ P.axisSwap.shift (shiftSwap i) '' (S : Set V) := by
      simpa [shiftSwap, PeriodicGraph.axisSwap, siteAxisSwap_swap] using hx
    have hmem := hsub hx'
    rw [E.axisSwap_rectVertices] at hmem
    exact hmem
  · have hshiftSet :
        P.axisSwap.shift (shiftSwap i) '' (S : Set V) =
          P.shift (shift i) '' (S : Set V) := by
      ext x
      simp [shiftSwap, PeriodicGraph.axisSwap, siteAxisSwap_swap]
    change (mu.real (P.axisSwap.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
      mu.real (E.axisSwap.rectSideConnectionEvent
        (-(r + radius)) (-r) (-(radius : Real)) radius
        (P.axisSwap.shift (shiftSwap i) '' (S : Set V))
        (E.axisSwap.rectRightBoundaryVertices
          (-(r + radius)) (-r) (-(radius : Real)) radius)) at hprob
    rw [hhit, hshiftSet] at hprob
    rw [E.axisSwap_rightBoundaryEvent] at hprob
    exact hprob



theorem PeriodicPlaneEmbedding.leftBoundaryExhaustion_to_commonSquare
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (radius M : Nat) (hM : radius ≤ M) (S : Set V) (p : Real)
    (hS : S ⊆ E.rectVertices 0 radius (-(radius : Real)) radius)
    (hp : p < mu.real (E.rectSideConnectionEvent
      0 radius (-(radius : Real)) radius S
      (E.rectLeftBoundaryVertices 0 radius (-(radius : Real)) radius))) :
    P.shift (horizontalShift (-(M : Int))) '' S ⊆
        E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        (P.shift (horizontalShift (-(M : Int))) '' S)
        (E.rectLeftBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M)) := by
  let z := horizontalShift (-(M : Int))
  have hMr : (radius : Real) ≤ M := by exact_mod_cast hM
  have hz0 : (z 0 : Real) = -(M : Real) := by simp [z, horizontalShift]
  have hz1 : (z 1 : Real) = 0 := by simp [z, horizontalShift]
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := (E.shift_mem_rectVertices z 0 radius
      (-(radius : Real)) radius x).2 (hS hx)
    rw [hz0, hz1] at hx'
    norm_num at hx'
    exact E.rectVertices_mono (le_refl (-(M : Real))) (by linarith)
      (by linarith) (by linarith) hx'
  · have htranslate := E.rectLeftConnection_translate_measureReal_eq
      mu hTI z 0 radius (-(radius : Real)) radius S
    rw [hz0, hz1] at htranslate
    norm_num at htranslate
    have hmono : mu.real (E.rectSideConnectionEvent
        (-(M : Real)) (radius - M) (-(radius : Real)) radius
        (P.shift z '' S)
        (E.rectLeftBoundaryVertices (-(M : Real)) (radius - M)
          (-(radius : Real)) radius)) ≤
      mu.real (E.rectSideConnectionEvent (-(M : Real)) M (-(M : Real)) M
        (P.shift z '' S)
        (E.rectLeftBoundaryVertices (-(M : Real)) M (-(M : Real)) M)) :=
      measureReal_mono (E.rectLeftConnectionEvent_mono_otherBounds
      (a := -(M : Real)) (b := radius - M) (c := -(radius : Real))
      (d := radius) (b' := M) (c' := -(M : Real)) (d' := M)
      (P.shift z '' S) (by linarith) (by linarith) (by linarith))
    rw [← htranslate] at hp
    exact hp.trans_le (by
      simpa only [z, sub_eq_add_neg, add_comm] using hmono)


theorem PeriodicPlaneEmbedding.rightBoundaryExhaustion_to_commonSquare
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (radius M : Nat) (hM : radius ≤ M) (S : Set V) (p : Real)
    (hS : S ⊆ E.rectVertices (-(radius : Real)) 0
      (-(radius : Real)) radius)
    (hp : p < mu.real (E.rectSideConnectionEvent
      (-(radius : Real)) 0 (-(radius : Real)) radius S
      (E.rectRightBoundaryVertices
        (-(radius : Real)) 0 (-(radius : Real)) radius))) :
    P.shift (horizontalShift (M : Int)) '' S ⊆
        E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        (P.shift (horizontalShift (M : Int)) '' S)
        (E.rectRightBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M)) := by
  let z := horizontalShift (M : Int)
  have hMr : (radius : Real) ≤ M := by exact_mod_cast hM
  have hz0 : (z 0 : Real) = M := by simp [z, horizontalShift]
  have hz1 : (z 1 : Real) = 0 := by simp [z, horizontalShift]
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := (E.shift_mem_rectVertices z (-(radius : Real)) 0
      (-(radius : Real)) radius x).2 (hS hx)
    rw [hz0, hz1] at hx'
    norm_num at hx'
    exact E.rectVertices_mono (by linarith) (le_refl (M : Real))
      (by linarith) (by linarith) hx'
  · have htranslate := E.rectRightConnection_translate_measureReal_eq
      mu hTI z (-(radius : Real)) 0 (-(radius : Real)) radius S
    rw [hz0, hz1] at htranslate
    norm_num at htranslate
    have hmono : mu.real (E.rectSideConnectionEvent
        (M - radius) M (-(radius : Real)) radius (P.shift z '' S)
        (E.rectRightBoundaryVertices (M - radius) M
          (-(radius : Real)) radius)) ≤
      mu.real (E.rectSideConnectionEvent (-(M : Real)) M (-(M : Real)) M
        (P.shift z '' S)
        (E.rectRightBoundaryVertices (-(M : Real)) M (-(M : Real)) M)) :=
      measureReal_mono (E.rectRightConnectionEvent_mono_otherBounds
      (a := M - radius) (b := (M : Real)) (c := -(radius : Real))
      (d := radius) (a' := -(M : Real)) (c' := -(M : Real)) (d' := M)
      (P.shift z '' S) (by linarith) (by linarith) (by linarith))
    rw [← htranslate] at hp
    exact hp.trans_le (by
      simpa only [z, sub_eq_add_neg, add_comm] using hmono)


theorem PeriodicPlaneEmbedding.bottomBoundaryExhaustion_to_commonSquare
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (radius M : Nat) (hM : radius ≤ M) (S : Set V) (p : Real)
    (hS : S ⊆ E.rectVertices (-(radius : Real)) radius 0 radius)
    (hp : p < mu.real (E.rectSideConnectionEvent
      (-(radius : Real)) radius 0 radius S
      (E.rectBottomBoundaryVertices
        (-(radius : Real)) radius 0 radius))) :
    P.shift (verticalShift (-(M : Int))) '' S ⊆
        E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        (P.shift (verticalShift (-(M : Int))) '' S)
        (E.rectBottomBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M)) := by
  let z := verticalShift (-(M : Int))
  have hMr : (radius : Real) ≤ M := by exact_mod_cast hM
  have hz0 : (z 0 : Real) = 0 := by simp [z, verticalShift]
  have hz1 : (z 1 : Real) = -(M : Real) := by simp [z, verticalShift]
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := (E.shift_mem_rectVertices z (-(radius : Real)) radius
      0 radius x).2 (hS hx)
    rw [hz0, hz1] at hx'
    norm_num at hx'
    exact E.rectVertices_mono (by linarith) (by linarith)
      (le_refl (-(M : Real))) (by linarith) hx'
  · have htranslate := E.rectBottomConnection_translate_measureReal_eq
      mu hTI z (-(radius : Real)) radius 0 radius S
    rw [hz0, hz1] at htranslate
    norm_num at htranslate
    have hmono : mu.real (E.rectSideConnectionEvent
        (-(radius : Real)) radius (-(M : Real)) (radius - M)
        (P.shift z '' S)
        (E.rectBottomBoundaryVertices (-(radius : Real)) radius
          (-(M : Real)) (radius - M))) ≤
      mu.real (E.rectSideConnectionEvent (-(M : Real)) M (-(M : Real)) M
        (P.shift z '' S)
        (E.rectBottomBoundaryVertices (-(M : Real)) M (-(M : Real)) M)) :=
      measureReal_mono (E.rectBottomConnectionEvent_mono_otherBounds
      (a := -(radius : Real)) (b := radius) (c := -(M : Real))
      (d := radius - M) (a' := -(M : Real)) (b' := M) (d' := M)
      (P.shift z '' S) (by linarith) (by linarith) (by linarith))
    rw [← htranslate] at hp
    exact hp.trans_le hmono


theorem PeriodicPlaneEmbedding.topBoundaryExhaustion_to_commonSquare
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (radius M : Nat) (hM : radius ≤ M) (S : Set V) (p : Real)
    (hS : S ⊆ E.rectVertices (-(radius : Real)) radius
      (-(radius : Real)) 0)
    (hp : p < mu.real (E.rectSideConnectionEvent
      (-(radius : Real)) radius (-(radius : Real)) 0 S
      (E.rectTopBoundaryVertices
        (-(radius : Real)) radius (-(radius : Real)) 0))) :
    P.shift (verticalShift (M : Int)) '' S ⊆
        E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        (P.shift (verticalShift (M : Int)) '' S)
        (E.rectTopBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M)) := by
  let z := verticalShift (M : Int)
  have hMr : (radius : Real) ≤ M := by exact_mod_cast hM
  have hz0 : (z 0 : Real) = 0 := by simp [z, verticalShift]
  have hz1 : (z 1 : Real) = M := by simp [z, verticalShift]
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := (E.shift_mem_rectVertices z (-(radius : Real)) radius
      (-(radius : Real)) 0 x).2 (hS hx)
    rw [hz0, hz1] at hx'
    norm_num at hx'
    exact E.rectVertices_mono (by linarith) (by linarith)
      (by linarith) (le_refl (M : Real)) hx'
  · have htranslate := E.rectTopConnection_translate_measureReal_eq
      mu hTI z (-(radius : Real)) radius (-(radius : Real)) 0 S
    rw [hz0, hz1] at htranslate
    norm_num at htranslate
    have hmono : mu.real (E.rectSideConnectionEvent
        (-(radius : Real)) radius (M - radius) M (P.shift z '' S)
        (E.rectTopBoundaryVertices (-(radius : Real)) radius
          (M - radius) M)) ≤
      mu.real (E.rectSideConnectionEvent (-(M : Real)) M (-(M : Real)) M
        (P.shift z '' S)
        (E.rectTopBoundaryVertices (-(M : Real)) M (-(M : Real)) M)) :=
      measureReal_mono (E.rectTopConnectionEvent_mono_otherBounds
      (a := -(radius : Real)) (b := radius) (c := M - radius)
      (d := (M : Real)) (a' := -(M : Real)) (b' := M) (c' := -(M : Real))
      (P.shift z '' S) (by linarith) (by linarith) (by linarith))
    rw [← htranslate] at hp
    exact hp.trans_le (by
      simpa only [z, sub_eq_add_neg, add_comm] using hmono)



def commonPrimalDualBandHalfWidth
    (primalLeft primalRight primalBottom primalTop
      dualLeft dualRight dualBottom dualTop : Nat) : Nat :=
  max (max (max primalLeft primalRight) (max primalBottom primalTop))
    (max (max dualLeft dualRight) (max dualBottom dualTop))

theorem le_commonPrimalDualBandHalfWidth
    (primalLeft primalRight primalBottom primalTop
      dualLeft dualRight dualBottom dualTop : Nat) :
    let M := commonPrimalDualBandHalfWidth
      primalLeft primalRight primalBottom primalTop
      dualLeft dualRight dualBottom dualTop
    primalLeft ≤ M ∧ primalRight ≤ M ∧
    primalBottom ≤ M ∧ primalTop ≤ M ∧
    dualLeft ≤ M ∧ dualRight ≤ M ∧
    dualBottom ≤ M ∧ dualTop ≤ M := by
  simp [commonPrimalDualBandHalfWidth]


noncomputable def boundaryBandPreferenceColor
    (margin extent position : Nat) (epsilon preferred opposite : Real) : Bool :=
  if position ≤ margin then true
  else if extent ≤ position + margin then false
  else decide (opposite ≤ preferred + epsilon)

@[simp] theorem boundaryBandPreferenceColor_eq_true_of_lower
    {margin extent position : Nat} {epsilon preferred opposite : Real}
    (hposition : position ≤ margin) :
    boundaryBandPreferenceColor margin extent position
      epsilon preferred opposite = true := by
  simp [boundaryBandPreferenceColor, hposition]

@[simp] theorem boundaryBandPreferenceColor_eq_false_of_upper
    {margin extent position : Nat} {epsilon preferred opposite : Real}
    (hsep : 2 * margin < extent)
    (hposition : extent ≤ position + margin) :
    boundaryBandPreferenceColor margin extent position
      epsilon preferred opposite = false := by
  have hnot : ¬position ≤ margin := by omega
  simp [boundaryBandPreferenceColor, hnot, hposition]



theorem boundaryBandPreferenceColor_true_imp
    {margin extent position : Nat} {epsilon preferred opposite p : Real}
    (hepsilon : 0 ≤ epsilon) (hsep : 2 * margin < extent)
    (hopposite : opposite ≤ 1)
    (hlower : position ≤ margin → p ≤ preferred)
    (hdefect : 1 - p ≤ epsilon)
    (hcolor : boundaryBandPreferenceColor margin extent position
      epsilon preferred opposite = true) :
    opposite ≤ preferred + epsilon := by
  by_cases hlowerBand : position ≤ margin
  · linarith [hlower hlowerBand]
  by_cases hupperBand : extent ≤ position + margin
  · simp [boundaryBandPreferenceColor, hlowerBand, hupperBand] at hcolor
  · have hdecide : decide (opposite ≤ preferred + epsilon) = true := by
      simpa [boundaryBandPreferenceColor, hlowerBand, hupperBand] using hcolor
    exact of_decide_eq_true hdecide



theorem boundaryBandPreferenceColor_false_imp
    {margin extent position : Nat} {epsilon preferred opposite p : Real}
    (hepsilon : 0 ≤ epsilon) (hsep : 2 * margin < extent)
    (hpreferred : preferred ≤ 1)
    (hupper : extent ≤ position + margin → p ≤ opposite)
    (hdefect : 1 - p ≤ epsilon)
    (hcolor : boundaryBandPreferenceColor margin extent position
      epsilon preferred opposite = false) :
    preferred ≤ opposite + epsilon := by
  by_cases hlowerBand : position ≤ margin
  · simp [boundaryBandPreferenceColor, hlowerBand] at hcolor
  by_cases hupperBand : extent ≤ position + margin
  · linarith [hupper hupperBand]
  · have hdecide : decide (opposite ≤ preferred + epsilon) = false := by
      simpa [boundaryBandPreferenceColor, hlowerBand, hupperBand] using hcolor
    have hnot : ¬opposite ≤ preferred + epsilon := of_decide_eq_false hdecide
    linarith

end StatMech.FK.PeriodicPlanar
