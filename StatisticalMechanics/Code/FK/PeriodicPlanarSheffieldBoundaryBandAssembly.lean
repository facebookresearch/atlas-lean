/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldBoundaryBandPadding
import Code.FK.PeriodicPlanarSheffieldExclusion
import Code.FK.PeriodicPlanarSheffieldDeepTemplateGridAssembly










open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}





theorem PeriodicPlaneEmbedding.exists_translatedFamily_leftBoundaryExhaustion_centered
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (shift : ι → Site 2)
    (hinside : ∀ i,
      P.shift (shift i) '' (S : Set V) ⊆ E.rightHalfPlaneVertices r)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ i,
      P.shift (shift i) '' (S : Set V) ⊆
          E.rectVertices r (r + radius)
            ((shift i 1 : Real) - radius) ((shift i 1 : Real) + radius) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent r (r + radius)
          ((shift i 1 : Real) - radius) ((shift i 1 : Real) + radius)
          (P.shift (shift i) '' (S : Set V))
          (E.rectLeftBoundaryVertices r (r + radius)
            ((shift i 1 : Real) - radius)
            ((shift i 1 : Real) + radius))) := by
  let normalized : ι → Site 2 := fun i =>
    shift i + verticalShift (-(shift i 1))
  have hnormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) =
        P.shift (verticalShift (-(shift i 1))) ''
          (P.shift (shift i) '' (S : Set V)) := by
    rw [P.shift_image_shift]
  have hinsideNormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) ⊆
        E.rightHalfPlaneVertices r := by
    rw [hnormalized]
    exact E.shift_image_rightHalfPlaneVertices_vertical
      (-(shift i 1)) r ▸ Set.image_mono (hinside i)
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normalized hinsideNormalized hepsilon
  refine ⟨radius, ?_⟩
  intro i
  let z := verticalShift (shift i 1)
  have hz0 : (z 0 : Real) = 0 := by simp [z, verticalShift]
  have hz1 : (z 1 : Real) = shift i 1 := by simp [z, verticalShift]
  have horiginal :
      P.shift z '' (P.shift (normalized i) '' (S : Set V)) =
        P.shift (shift i) '' (S : Set V) := by
    rw [P.shift_image_shift]
    apply congrArg (fun w : Site 2 => P.shift w '' (S : Set V))
    dsimp only [normalized, z]
    funext k
    fin_cases k <;> simp [verticalShift]
  constructor
  · intro x hx
    rw [← horiginal] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z r (r + radius)
      (-(radius : Real)) radius y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have htranslate := E.rectLeftConnection_translate_measureReal_eq
      mu hTI z r (r + radius) (-(radius : Real)) radius
      (P.shift (normalized i) '' (S : Set V))
    rw [hz0, hz1, horiginal] at htranslate
    have hp := (hradius i).2
    change (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
      mu.real (E.rectSideConnectionEvent r (r + radius)
        (-(radius : Real)) radius
        (P.shift (normalized i) '' (S : Set V))
        (E.rectLeftBoundaryVertices r (r + radius)
          (-(radius : Real)) radius)) at hp
    rw [← htranslate] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp




theorem PeriodicPlaneEmbedding.exists_leftBoundaryExhaustion_uniform_tangentialPlacement
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (normal : ι → Site 2)
    (hinside : ∀ i,
      P.shift (normal i) '' (S : Set V) ⊆ E.rightHalfPlaneVertices r)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ tangent : ι → Int, ∀ i,
      let shift := normal i + verticalShift (tangent i)
      P.shift shift '' (S : Set V) ⊆
          E.rectVertices r (r + radius)
            ((tangent i : Real) - radius) ((tangent i : Real) + radius) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent r (r + radius)
          ((tangent i : Real) - radius) ((tangent i : Real) + radius)
          (P.shift shift '' (S : Set V))
          (E.rectLeftBoundaryVertices r (r + radius)
            ((tangent i : Real) - radius) ((tangent i : Real) + radius))) := by
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normal hinside hepsilon
  refine ⟨radius, ?_⟩
  intro tangent i
  dsimp only
  let z := verticalShift (tangent i)
  have hz0 : (z 0 : Real) = 0 := by simp [z]
  have hz1 : (z 1 : Real) = tangent i := by simp [z]
  have himage :
      P.shift z '' (P.shift (normal i) '' (S : Set V)) =
        P.shift (normal i + verticalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · intro x hx
    rw [← himage] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z r (r + radius)
      (-(radius : Real)) radius y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have htranslate := E.rectLeftConnection_translate_measureReal_eq
      mu hTI z r (r + radius) (-(radius : Real)) radius
      (P.shift (normal i) '' (S : Set V))
    rw [hz0, hz1, himage] at htranslate
    have hp := (hradius i).2
    change (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
      mu.real (E.rectSideConnectionEvent r (r + radius)
        (-(radius : Real)) radius (P.shift (normal i) '' (S : Set V))
        (E.rectLeftBoundaryVertices r (r + radius)
          (-(radius : Real)) radius)) at hp
    rw [← htranslate] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.exists_translatedFamily_rightBoundaryExhaustion_centered
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
            ((shift i 1 : Real) - radius) ((shift i 1 : Real) + radius) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent (-(r + radius)) (-r)
          ((shift i 1 : Real) - radius) ((shift i 1 : Real) + radius)
          (P.shift (shift i) '' (S : Set V))
          (E.rectRightBoundaryVertices (-(r + radius)) (-r)
            ((shift i 1 : Real) - radius)
            ((shift i 1 : Real) + radius))) := by
  let normalized : ι → Site 2 := fun i =>
    shift i + verticalShift (-(shift i 1))
  have hnormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) =
        P.shift (verticalShift (-(shift i 1))) ''
          (P.shift (shift i) '' (S : Set V)) := by
    rw [P.shift_image_shift]
  have hinsideNormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) ⊆
        {v | E.vertexCoord v 0 ≤ -r} := by
    rw [hnormalized]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h := hinside i hy
    simpa [E.vertexCoord_shift, verticalShift] using h
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normalized hinsideNormalized hepsilon
  refine ⟨radius, ?_⟩
  intro i
  let z := verticalShift (shift i 1)
  have hz0 : (z 0 : Real) = 0 := by simp [z]
  have hz1 : (z 1 : Real) = shift i 1 := by simp [z]
  have horiginal :
      P.shift z '' (P.shift (normalized i) '' (S : Set V)) =
        P.shift (shift i) '' (S : Set V) := by
    rw [P.shift_image_shift]
    apply congrArg (fun w : Site 2 => P.shift w '' (S : Set V))
    dsimp only [normalized, z]
    funext k
    fin_cases k <;> simp [verticalShift]
  constructor
  · intro x hx
    rw [← horiginal] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(r + radius)) (-r)
      (-(radius : Real)) radius y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have htranslate := E.rectRightConnection_translate_measureReal_eq
      mu hTI z (-(r + radius)) (-r) (-(radius : Real)) radius
      (P.shift (normalized i) '' (S : Set V))
    rw [hz0, hz1, horiginal] at htranslate
    have hp := (hradius i).2
    rw [← htranslate] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.exists_translatedFamily_bottomBoundaryExhaustion_centered
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
          E.rectVertices ((shift i 0 : Real) - radius)
            ((shift i 0 : Real) + radius) r (r + radius) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent
          ((shift i 0 : Real) - radius) ((shift i 0 : Real) + radius)
          r (r + radius) (P.shift (shift i) '' (S : Set V))
          (E.rectBottomBoundaryVertices
            ((shift i 0 : Real) - radius) ((shift i 0 : Real) + radius)
            r (r + radius))) := by
  let normalized : ι → Site 2 := fun i =>
    shift i + horizontalShift (-(shift i 0))
  have hnormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) =
        P.shift (horizontalShift (-(shift i 0))) ''
          (P.shift (shift i) '' (S : Set V)) := by
    rw [P.shift_image_shift]
  have hinsideNormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) ⊆
        {v | r ≤ E.vertexCoord v 1} := by
    rw [hnormalized]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h := hinside i hy
    simpa [E.vertexCoord_shift, horizontalShift] using h
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_bottomBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normalized hinsideNormalized hepsilon
  refine ⟨radius, ?_⟩
  intro i
  let z := horizontalShift (shift i 0)
  have hz0 : (z 0 : Real) = shift i 0 := by simp [z]
  have hz1 : (z 1 : Real) = 0 := by simp [z]
  have horiginal :
      P.shift z '' (P.shift (normalized i) '' (S : Set V)) =
        P.shift (shift i) '' (S : Set V) := by
    rw [P.shift_image_shift]
    apply congrArg (fun w : Site 2 => P.shift w '' (S : Set V))
    dsimp only [normalized, z]
    funext k
    fin_cases k <;> simp [horizontalShift]
  constructor
  · intro x hx
    rw [← horiginal] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(radius : Real)) radius
      r (r + radius) y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have htranslate := E.rectBottomConnection_translate_measureReal_eq
      mu hTI z (-(radius : Real)) radius r (r + radius)
      (P.shift (normalized i) '' (S : Set V))
    rw [hz0, hz1, horiginal] at htranslate
    have hp := (hradius i).2
    rw [← htranslate] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.exists_translatedFamily_topBoundaryExhaustion_centered
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
          E.rectVertices ((shift i 0 : Real) - radius)
            ((shift i 0 : Real) + radius) (-(r + radius)) (-r) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent
          ((shift i 0 : Real) - radius) ((shift i 0 : Real) + radius)
          (-(r + radius)) (-r) (P.shift (shift i) '' (S : Set V))
          (E.rectTopBoundaryVertices
            ((shift i 0 : Real) - radius) ((shift i 0 : Real) + radius)
            (-(r + radius)) (-r))) := by
  let normalized : ι → Site 2 := fun i =>
    shift i + horizontalShift (-(shift i 0))
  have hnormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) =
        P.shift (horizontalShift (-(shift i 0))) ''
          (P.shift (shift i) '' (S : Set V)) := by
    rw [P.shift_image_shift]
  have hinsideNormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) ⊆
        {v | E.vertexCoord v 1 ≤ -r} := by
    rw [hnormalized]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h := hinside i hy
    simpa [E.vertexCoord_shift, horizontalShift] using h
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_topBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normalized hinsideNormalized hepsilon
  refine ⟨radius, ?_⟩
  intro i
  let z := horizontalShift (shift i 0)
  have hz0 : (z 0 : Real) = shift i 0 := by simp [z]
  have hz1 : (z 1 : Real) = 0 := by simp [z]
  have horiginal :
      P.shift z '' (P.shift (normalized i) '' (S : Set V)) =
        P.shift (shift i) '' (S : Set V) := by
    rw [P.shift_image_shift]
    apply congrArg (fun w : Site 2 => P.shift w '' (S : Set V))
    dsimp only [normalized, z]
    funext k
    fin_cases k <;> simp [horizontalShift]
  constructor
  · intro x hx
    rw [← horiginal] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(radius : Real)) radius
      (-(r + radius)) (-r) y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have htranslate := E.rectTopConnection_translate_measureReal_eq
      mu hTI z (-(radius : Real)) radius (-(r + radius)) (-r)
      (P.shift (normalized i) '' (S : Set V))
    rw [hz0, hz1, horiginal] at htranslate
    have hp := (hradius i).2
    rw [← htranslate] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.exists_rightBoundaryExhaustion_uniform_tangentialPlacement
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (normal : ι → Site 2)
    (hinside : ∀ i, P.shift (normal i) '' (S : Set V) ⊆
      {v | E.vertexCoord v 0 ≤ -r})
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ tangent : ι → Int, ∀ i,
      let shift := normal i + verticalShift (tangent i)
      P.shift shift '' (S : Set V) ⊆
          E.rectVertices (-(r + radius)) (-r)
            ((tangent i : Real) - radius) ((tangent i : Real) + radius) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent (-(r + radius)) (-r)
          ((tangent i : Real) - radius) ((tangent i : Real) + radius)
          (P.shift shift '' (S : Set V))
          (E.rectRightBoundaryVertices (-(r + radius)) (-r)
            ((tangent i : Real) - radius) ((tangent i : Real) + radius))) := by
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normal hinside hepsilon
  refine ⟨radius, ?_⟩
  intro tangent i
  dsimp only
  let z := verticalShift (tangent i)
  have hz0 : (z 0 : Real) = 0 := by simp [z]
  have hz1 : (z 1 : Real) = tangent i := by simp [z]
  have himage : P.shift z '' (P.shift (normal i) '' (S : Set V)) =
      P.shift (normal i + verticalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · rintro x hx
    rw [← himage] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(r + radius)) (-r)
      (-(radius : Real)) radius y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have ht := E.rectRightConnection_translate_measureReal_eq mu hTI z
      (-(r + radius)) (-r) (-(radius : Real)) radius
      (P.shift (normal i) '' (S : Set V))
    rw [hz0, hz1, himage] at ht
    have hp := (hradius i).2
    rw [← ht] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.exists_bottomBoundaryExhaustion_uniform_tangentialPlacement
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (normal : ι → Site 2)
    (hinside : ∀ i, P.shift (normal i) '' (S : Set V) ⊆
      {v | r ≤ E.vertexCoord v 1})
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ tangent : ι → Int, ∀ i,
      let shift := normal i + horizontalShift (tangent i)
      P.shift shift '' (S : Set V) ⊆
          E.rectVertices ((tangent i : Real) - radius)
            ((tangent i : Real) + radius) r (r + radius) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent
          ((tangent i : Real) - radius) ((tangent i : Real) + radius)
          r (r + radius) (P.shift shift '' (S : Set V))
          (E.rectBottomBoundaryVertices
            ((tangent i : Real) - radius) ((tangent i : Real) + radius)
            r (r + radius))) := by
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_bottomBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normal hinside hepsilon
  refine ⟨radius, ?_⟩
  intro tangent i
  dsimp only
  let z := horizontalShift (tangent i)
  have hz0 : (z 0 : Real) = tangent i := by simp [z]
  have hz1 : (z 1 : Real) = 0 := by simp [z]
  have himage : P.shift z '' (P.shift (normal i) '' (S : Set V)) =
      P.shift (normal i + horizontalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · rintro x hx
    rw [← himage] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(radius : Real)) radius
      r (r + radius) y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have ht := E.rectBottomConnection_translate_measureReal_eq mu hTI z
      (-(radius : Real)) radius r (r + radius)
      (P.shift (normal i) '' (S : Set V))
    rw [hz0, hz1, himage] at ht
    have hp := (hradius i).2
    rw [← ht] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.exists_topBoundaryExhaustion_uniform_tangentialPlacement
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (normal : ι → Site 2)
    (hinside : ∀ i, P.shift (normal i) '' (S : Set V) ⊆
      {v | E.vertexCoord v 1 ≤ -r})
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ tangent : ι → Int, ∀ i,
      let shift := normal i + horizontalShift (tangent i)
      P.shift shift '' (S : Set V) ⊆
          E.rectVertices ((tangent i : Real) - radius)
            ((tangent i : Real) + radius) (-(r + radius)) (-r) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent
          ((tangent i : Real) - radius) ((tangent i : Real) + radius)
          (-(r + radius)) (-r) (P.shift shift '' (S : Set V))
          (E.rectTopBoundaryVertices
            ((tangent i : Real) - radius) ((tangent i : Real) + radius)
            (-(r + radius)) (-r))) := by
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_topBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normal hinside hepsilon
  refine ⟨radius, ?_⟩
  intro tangent i
  dsimp only
  let z := horizontalShift (tangent i)
  have hz0 : (z 0 : Real) = tangent i := by simp [z]
  have hz1 : (z 1 : Real) = 0 := by simp [z]
  have himage : P.shift z '' (P.shift (normal i) '' (S : Set V)) =
      P.shift (normal i + horizontalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · rintro x hx
    rw [← himage] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(radius : Real)) radius
      (-(r + radius)) (-r) y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have ht := E.rectTopConnection_translate_measureReal_eq mu hTI z
      (-(radius : Real)) radius (-(r + radius)) (-r)
      (P.shift (normal i) '' (S : Set V))
    rw [hz0, hz1, himage] at ht
    have hp := (hradius i).2
    rw [← ht] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp



structure PeriodicPlaneEmbedding.BoundaryBandSeed
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Finset V) (width height : Nat) (p : Real) where
  baseLeft : Site 2
  baseRight : Site 2
  baseBottom : Site 2
  baseTop : Site 2
  radiusLeft : Nat
  radiusRight : Nat
  radiusBottom : Nat
  radiusTop : Nat
  left : ∀ v : PreferenceGridVertex width height,
    P.shift (baseLeft + preferenceGridSite v) '' (S : Set V) ⊆
        E.rectVertices 0 radiusLeft (-(radiusLeft : Real)) radiusLeft ∧
      p < mu.real (E.rectSideConnectionEvent
        0 radiusLeft (-(radiusLeft : Real)) radiusLeft
        (P.shift (baseLeft + preferenceGridSite v) '' (S : Set V))
        (E.rectLeftBoundaryVertices
          0 radiusLeft (-(radiusLeft : Real)) radiusLeft))
  right : ∀ v : PreferenceGridVertex width height,
    P.shift (baseRight + preferenceGridSite v) '' (S : Set V) ⊆
        E.rectVertices (-(radiusRight : Real)) 0
          (-(radiusRight : Real)) radiusRight ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusRight : Real)) 0 (-(radiusRight : Real)) radiusRight
        (P.shift (baseRight + preferenceGridSite v) '' (S : Set V))
        (E.rectRightBoundaryVertices
          (-(radiusRight : Real)) 0 (-(radiusRight : Real)) radiusRight))
  bottom : ∀ v : PreferenceGridVertex width height,
    P.shift (baseBottom + preferenceGridSite v) '' (S : Set V) ⊆
        E.rectVertices (-(radiusBottom : Real)) radiusBottom
          0 radiusBottom ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusBottom : Real)) radiusBottom 0 radiusBottom
        (P.shift (baseBottom + preferenceGridSite v) '' (S : Set V))
        (E.rectBottomBoundaryVertices
          (-(radiusBottom : Real)) radiusBottom 0 radiusBottom))
  top : ∀ v : PreferenceGridVertex width height,
    P.shift (baseTop + preferenceGridSite v) '' (S : Set V) ⊆
        E.rectVertices (-(radiusTop : Real)) radiusTop
          (-(radiusTop : Real)) 0 ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusTop : Real)) radiusTop (-(radiusTop : Real)) 0
        (P.shift (baseTop + preferenceGridSite v) '' (S : Set V))
        (E.rectTopBoundaryVertices
          (-(radiusTop : Real)) radiusTop (-(radiusTop : Real)) 0))



theorem PeriodicPlaneEmbedding.exists_orbitBox_boundaryBandSeed
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (N width height : Nat) {delta : Real} (hdelta : 0 < delta) :
    Nonempty (E.BoundaryBandSeed mu (P.orbitBox N) width height
      ((mu.real (P.setHitsInfinite (P.orbitBox N : Set V))) ^ 2 - delta)) := by
  classical
  obtain ⟨baseLeft, hbaseLeft⟩ :=
    E.exists_shift_orbitBox_subset_rightHalfPlane N 0
  obtain ⟨baseRight, hbaseRight⟩ :=
    E.exists_shift_orbitBox_subset_leftComplement N (-(width : Real))
  obtain ⟨baseBottomSwap, hbaseBottom⟩ :=
    E.axisSwap.exists_shift_orbitBox_subset_rightHalfPlane N 0
  obtain ⟨baseTopSwap, hbaseTop⟩ :=
    E.axisSwap.exists_shift_orbitBox_subset_leftComplement N (-(height : Real))
  let baseBottom := siteAxisSwap baseBottomSwap
  let baseTop := siteAxisSwap baseTopSwap
  have hinsideLeft (v : PreferenceGridVertex width height) :
      P.shift (baseLeft + preferenceGridSite v) ''
          (P.orbitBox N : Set V) ⊆ E.rightHalfPlaneVertices 0 := by
    rintro _ ⟨u, hu, rfl⟩
    have huLeft := hbaseLeft u hu
    change 0 ≤ E.vertexCoord (P.shift baseLeft u) 0 at huLeft
    simp only [E.vertexCoord_shift] at huLeft
    change 0 ≤ E.vertexCoord
      (P.shift (baseLeft + preferenceGridSite v) u) 0
    simp only [P.shift_add, E.vertexCoord_shift, preferenceGridSite]
    norm_num
    exact add_nonneg huLeft (by positivity)
  have hinsideRight (v : PreferenceGridVertex width height) :
      P.shift (baseRight + preferenceGridSite v) ''
          (P.orbitBox N : Set V) ⊆ {u | E.vertexCoord u 0 ≤ 0} := by
    rintro _ ⟨u, hu, rfl⟩
    have huRight := hbaseRight u hu
    change ¬ (-(width : Real) ≤
      E.vertexCoord (P.shift baseRight u) 0) at huRight
    change E.vertexCoord
      (P.shift (baseRight + preferenceGridSite v) u) 0 ≤ 0
    have hv : (v.1.val : Real) ≤ width := by
      exact_mod_cast Nat.le_of_lt_succ v.1.isLt
    simp only [E.vertexCoord_shift] at huRight
    simp only [P.shift_add, E.vertexCoord_shift, preferenceGridSite]
    norm_num
    linarith
  have hinsideBottom (v : PreferenceGridVertex width height) :
      P.shift (baseBottom + preferenceGridSite v) ''
          (P.orbitBox N : Set V) ⊆ {u | 0 ≤ E.vertexCoord u 1} := by
    rintro _ ⟨u, hu, rfl⟩
    have huBottom := hbaseBottom u (by
      rw [P.axisSwap_orbitBox]
      exact hu)
    change 0 ≤ E.axisSwap.vertexCoord
      (P.axisSwap.shift baseBottomSwap u) 0 at huBottom
    have huBottom' : 0 ≤ E.vertexCoord (P.shift baseBottom u) 1 := by
      simpa [baseBottom, PeriodicGraph.axisSwap] using huBottom
    simp only [E.vertexCoord_shift] at huBottom'
    change 0 ≤ E.vertexCoord
      (P.shift (baseBottom + preferenceGridSite v) u) 1
    simp only [P.shift_add, E.vertexCoord_shift, preferenceGridSite]
    norm_num
    exact add_nonneg huBottom' (by positivity)
  have hinsideTop (v : PreferenceGridVertex width height) :
      P.shift (baseTop + preferenceGridSite v) ''
          (P.orbitBox N : Set V) ⊆ {u | E.vertexCoord u 1 ≤ 0} := by
    rintro _ ⟨u, hu, rfl⟩
    have huTop := hbaseTop u (by
      rw [P.axisSwap_orbitBox]
      exact hu)
    change ¬ (-(height : Real) ≤ E.axisSwap.vertexCoord
      (P.axisSwap.shift baseTopSwap u) 0) at huTop
    have huTop' : ¬ (-(height : Real) ≤
        E.vertexCoord (P.shift baseTop u) 1) := by
      simpa [baseTop, PeriodicGraph.axisSwap] using huTop
    change E.vertexCoord
      (P.shift (baseTop + preferenceGridSite v) u) 1 ≤ 0
    have hv : (v.2.val : Real) ≤ height := by
      exact_mod_cast Nat.le_of_lt_succ v.2.isLt
    simp only [E.vertexCoord_shift] at huTop'
    simp only [P.shift_add, E.vertexCoord_shift, preferenceGridSite]
    norm_num
    linarith
  obtain ⟨radiusLeft, hleft⟩ :=
    E.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun v : PreferenceGridVertex width height =>
        baseLeft + preferenceGridSite v) hinsideLeft hdelta
  obtain ⟨radiusRight, hright⟩ :=
    E.exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun v : PreferenceGridVertex width height =>
        baseRight + preferenceGridSite v)
      (by simpa only [neg_zero] using hinsideRight) hdelta
  obtain ⟨radiusBottom, hbottom⟩ :=
    E.exists_translatedFamily_bottomBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun v : PreferenceGridVertex width height =>
        baseBottom + preferenceGridSite v) hinsideBottom hdelta
  obtain ⟨radiusTop, htop⟩ :=
    E.exists_translatedFamily_topBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun v : PreferenceGridVertex width height =>
        baseTop + preferenceGridSite v)
      (by simpa only [neg_zero] using hinsideTop) hdelta
  exact ⟨{
    baseLeft := baseLeft
    baseRight := baseRight
    baseBottom := baseBottom
    baseTop := baseTop
    radiusLeft := radiusLeft
    radiusRight := radiusRight
    radiusBottom := radiusBottom
    radiusTop := radiusTop
    left := by
      simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
        PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent] using hleft
    right := by simpa using hright
    bottom := by simpa using hbottom
    top := by simpa using htop }⟩




structure PeriodicPlaneEmbedding.CommonSquareBoundaryBandData
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Finset V) (width height M : Nat) (p : Real) where
  zLeft : Site 2
  zRight : Site 2
  zBottom : Site 2
  zTop : Site 2
  left : ∀ v : PreferenceGridVertex width height,
    ((S.image (P.shift zLeft)).image
        (P.shift (preferenceGridSite v)) : Set V) ⊆
          E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        ((S.image (P.shift zLeft)).image
          (P.shift (preferenceGridSite v)) : Set V)
        (E.rectLeftBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))
  right : ∀ v : PreferenceGridVertex width height,
    ((S.image (P.shift zRight)).image
        (P.shift (preferenceGridSite v)) : Set V) ⊆
          E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        ((S.image (P.shift zRight)).image
          (P.shift (preferenceGridSite v)) : Set V)
        (E.rectRightBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))
  bottom : ∀ v : PreferenceGridVertex width height,
    ((S.image (P.shift zBottom)).image
        (P.shift (preferenceGridSite v)) : Set V) ⊆
          E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        ((S.image (P.shift zBottom)).image
          (P.shift (preferenceGridSite v)) : Set V)
        (E.rectBottomBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))
  top : ∀ v : PreferenceGridVertex width height,
    ((S.image (P.shift zTop)).image
        (P.shift (preferenceGridSite v)) : Set V) ⊆
          E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        ((S.image (P.shift zTop)).image
          (P.shift (preferenceGridSite v)) : Set V)
        (E.rectTopBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))

omit [Countable V] in
theorem PeriodicGraph.componentGridImage_eq_normalShift
    (P : PeriodicGraph V) (S : Finset V)
    (base normal : Site 2) {width height : Nat}
    (v : PreferenceGridVertex width height) :
    ((S.image (P.shift (base + normal))).image
        (P.shift (preferenceGridSite v)) : Set V) =
      P.shift normal ''
        (P.shift (base + preferenceGridSite v) '' (S : Set V)) := by
  ext x
  constructor
  · intro hx
    change x ∈ (S.image (P.shift (base + normal))).image
      (P.shift (preferenceGridSite v)) at hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨P.shift (base + preferenceGridSite v) u,
      ⟨u, hu, rfl⟩, ?_⟩
    rw [← P.shift_add, ← P.shift_add]
    congr 2
    abel
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    change P.shift normal (P.shift (base + preferenceGridSite v) u) ∈
      (S.image (P.shift (base + normal))).image
        (P.shift (preferenceGridSite v))
    apply Finset.mem_image.mpr
    refine ⟨P.shift (base + normal) u, Finset.mem_image.mpr ⟨u, hu, rfl⟩, ?_⟩
    rw [← P.shift_add, ← P.shift_add]
    congr 2
    abel



def PeriodicPlaneEmbedding.BoundaryBandSeed.toCommonSquare
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {width height : Nat} {p : Real}
    (seed : E.BoundaryBandSeed mu S width height p)
    (M : Nat)
    (hleft : seed.radiusLeft ≤ M)
    (hright : seed.radiusRight ≤ M)
    (hbottom : seed.radiusBottom ≤ M)
    (htop : seed.radiusTop ≤ M) :
    E.CommonSquareBoundaryBandData mu S width height M p := by
  let zLeft := seed.baseLeft + horizontalShift (-(M : Int))
  let zRight := seed.baseRight + horizontalShift (M : Int)
  let zBottom := seed.baseBottom + verticalShift (-(M : Int))
  let zTop := seed.baseTop + verticalShift (M : Int)
  refine {
    zLeft := zLeft
    zRight := zRight
    zBottom := zBottom
    zTop := zTop
    left := ?_
    right := ?_
    bottom := ?_
    top := ?_ }
  · intro v
    have hv := E.leftBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusLeft M hleft
      (P.shift (seed.baseLeft + preferenceGridSite v) '' (S : Set V)) p
      (seed.left v).1 (seed.left v).2
    simpa only [zLeft, P.componentGridImage_eq_normalShift] using hv
  · intro v
    have hv := E.rightBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusRight M hright
      (P.shift (seed.baseRight + preferenceGridSite v) '' (S : Set V)) p
      (seed.right v).1 (seed.right v).2
    simpa only [zRight, P.componentGridImage_eq_normalShift] using hv
  · intro v
    have hv := E.bottomBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusBottom M hbottom
      (P.shift (seed.baseBottom + preferenceGridSite v) '' (S : Set V)) p
      (seed.bottom v).1 (seed.bottom v).2
    simpa only [zBottom, P.componentGridImage_eq_normalShift] using hv
  · intro v
    have hv := E.topBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusTop M htop
      (P.shift (seed.baseTop + preferenceGridSite v) '' (S : Set V)) p
      (seed.top v).1 (seed.top v).2
    simpa only [zTop, P.componentGridImage_eq_normalShift] using hv



theorem PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.template_subset
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    {S : Finset V} {width height M : Nat} {p : Real}
    (data : E.CommonSquareBoundaryBandData mu S width height M p)
    (v : PreferenceGridVertex width height) :
    ((P.fourShiftTemplate S data.zLeft data.zRight
        data.zBottom data.zTop).image
        (P.shift (preferenceGridSite v)) : Set V) ⊆
      E.rectVertices (-(M : Real)) M (-(M : Real)) M := by
  intro x hx
  change x ∈ (P.fourShiftTemplate S data.zLeft data.zRight
    data.zBottom data.zTop).image (P.shift (preferenceGridSite v)) at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  simp only [PeriodicGraph.fourShiftTemplate, Finset.mem_union] at hy
  rcases hy with (hy | hy) | (hy | hy)
  · exact (data.left v).1 (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  · exact (data.right v).1 (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  · exact (data.bottom v).1 (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  · exact (data.top v).1 (Finset.mem_image.mpr ⟨y, hy, rfl⟩)



theorem PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.leftScore_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {S : Finset V} {width height M : Nat} {p : Real}
    (data : E.CommonSquareBoundaryBandData mu S width height M p)
    (v : PreferenceGridVertex width height) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) M (-(M : Real)) M
      ((P.fourShiftTemplate S data.zLeft data.zRight
        data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices
        (-(M : Real)) M (-(M : Real)) M)) := by
  refine (data.left v).2.trans_le (measureReal_mono
    (E.rectSideConnectionEvent_mono_source ?_))
  intro x hx
  change x ∈ (S.image (P.shift data.zLeft)).image
    (P.shift (preferenceGridSite v)) at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨y,
    P.image_subset_fourShiftTemplate S data.zLeft data.zRight
      data.zBottom data.zTop hy, rfl⟩

theorem PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.rightScore_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {S : Finset V} {width height M : Nat} {p : Real}
    (data : E.CommonSquareBoundaryBandData mu S width height M p)
    (v : PreferenceGridVertex width height) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) M (-(M : Real)) M
      ((P.fourShiftTemplate S data.zLeft data.zRight
        data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices
        (-(M : Real)) M (-(M : Real)) M)) := by
  refine (data.right v).2.trans_le (measureReal_mono
    (E.rectSideConnectionEvent_mono_source ?_))
  intro x hx
  change x ∈ (S.image (P.shift data.zRight)).image
    (P.shift (preferenceGridSite v)) at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨y,
    P.image_right_subset_fourShiftTemplate S data.zLeft data.zRight
      data.zBottom data.zTop hy, rfl⟩

theorem PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.bottomScore_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {S : Finset V} {width height M : Nat} {p : Real}
    (data : E.CommonSquareBoundaryBandData mu S width height M p)
    (v : PreferenceGridVertex width height) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) M (-(M : Real)) M
      ((P.fourShiftTemplate S data.zLeft data.zRight
        data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices
        (-(M : Real)) M (-(M : Real)) M)) := by
  refine (data.bottom v).2.trans_le (measureReal_mono
    (E.rectSideConnectionEvent_mono_source ?_))
  intro x hx
  change x ∈ (S.image (P.shift data.zBottom)).image
    (P.shift (preferenceGridSite v)) at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨y,
    P.image_bottom_subset_fourShiftTemplate S data.zLeft data.zRight
      data.zBottom data.zTop hy, rfl⟩

theorem PeriodicPlaneEmbedding.CommonSquareBoundaryBandData.topScore_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {S : Finset V} {width height M : Nat} {p : Real}
    (data : E.CommonSquareBoundaryBandData mu S width height M p)
    (v : PreferenceGridVertex width height) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) M (-(M : Real)) M
      ((P.fourShiftTemplate S data.zLeft data.zRight
        data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices
        (-(M : Real)) M (-(M : Real)) M)) := by
  refine (data.top v).2.trans_le (measureReal_mono
    (E.rectSideConnectionEvent_mono_source ?_))
  intro x hx
  change x ∈ (S.image (P.shift data.zTop)).image
    (P.shift (preferenceGridSite v)) at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨y,
    P.image_top_subset_fourShiftTemplate S data.zLeft data.zRight
      data.zBottom data.zTop hy, rfl⟩

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}



theorem exists_matched_commonSquareBoundaryBandData
    (E : PeriodicPlaneEmbedding P)
    (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W))) [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {width height : Nat}
    {p pDual : Real}
    (primal : E.BoundaryBandSeed mu S width height p)
    (dual : Edual.BoundaryBandSeed muDual Sdual width height pDual) :
    ∃ M : Nat,
      Nonempty (E.CommonSquareBoundaryBandData
        mu S width height M p) ∧
      Nonempty (Edual.CommonSquareBoundaryBandData
        muDual Sdual width height M pDual) := by
  let M := commonPrimalDualBandHalfWidth
    primal.radiusLeft primal.radiusRight
    primal.radiusBottom primal.radiusTop
    dual.radiusLeft dual.radiusRight dual.radiusBottom dual.radiusTop
  have h := le_commonPrimalDualBandHalfWidth
    primal.radiusLeft primal.radiusRight
    primal.radiusBottom primal.radiusTop
    dual.radiusLeft dual.radiusRight dual.radiusBottom dual.radiusTop
  dsimp only at h
  exact ⟨M,
    ⟨primal.toCommonSquare E mu hTI M h.1 h.2.1 h.2.2.1 h.2.2.2.1⟩,
    ⟨dual.toCommonSquare Edual muDual hTIDual M
      h.2.2.2.2.1 h.2.2.2.2.2.1
      h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2⟩⟩




structure PeriodicPlaneEmbedding.NormalBoundaryBandSeed
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Finset V) (margin : Nat) (p : Real) where
  baseLeft : Site 2
  baseRight : Site 2
  baseBottom : Site 2
  baseTop : Site 2
  radiusLeft : Nat
  radiusRight : Nat
  radiusBottom : Nat
  radiusTop : Nat
  left : ∀ i : Fin (margin + 1),
    P.shift (baseLeft + horizontalShift i.val) '' (S : Set V) ⊆
        E.rectVertices 0 radiusLeft (-(radiusLeft : Real)) radiusLeft ∧
      p < mu.real (E.rectSideConnectionEvent
        0 radiusLeft (-(radiusLeft : Real)) radiusLeft
        (P.shift (baseLeft + horizontalShift i.val) '' (S : Set V))
        (E.rectLeftBoundaryVertices
          0 radiusLeft (-(radiusLeft : Real)) radiusLeft))
  right : ∀ i : Fin (margin + 1),
    P.shift (baseRight + horizontalShift (-(i.val : Int))) '' (S : Set V) ⊆
        E.rectVertices (-(radiusRight : Real)) 0
          (-(radiusRight : Real)) radiusRight ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusRight : Real)) 0 (-(radiusRight : Real)) radiusRight
        (P.shift (baseRight + horizontalShift (-(i.val : Int))) '' (S : Set V))
        (E.rectRightBoundaryVertices
          (-(radiusRight : Real)) 0 (-(radiusRight : Real)) radiusRight))
  bottom : ∀ i : Fin (margin + 1),
    P.shift (baseBottom + verticalShift i.val) '' (S : Set V) ⊆
        E.rectVertices (-(radiusBottom : Real)) radiusBottom
          0 radiusBottom ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusBottom : Real)) radiusBottom 0 radiusBottom
        (P.shift (baseBottom + verticalShift i.val) '' (S : Set V))
        (E.rectBottomBoundaryVertices
          (-(radiusBottom : Real)) radiusBottom 0 radiusBottom))
  top : ∀ i : Fin (margin + 1),
    P.shift (baseTop + verticalShift (-(i.val : Int))) '' (S : Set V) ⊆
        E.rectVertices (-(radiusTop : Real)) radiusTop
          (-(radiusTop : Real)) 0 ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusTop : Real)) radiusTop (-(radiusTop : Real)) 0
        (P.shift (baseTop + verticalShift (-(i.val : Int))) '' (S : Set V))
        (E.rectTopBoundaryVertices
          (-(radiusTop : Real)) radiusTop (-(radiusTop : Real)) 0))



theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.left_tangential
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (tangent : Fin (margin + 1) → Int) (i : Fin (margin + 1)) :
    let shift := seed.baseLeft + horizontalShift i.val +
      verticalShift (tangent i)
    P.shift shift '' (S : Set V) ⊆
        E.rectVertices 0 seed.radiusLeft
          ((tangent i : Real) - seed.radiusLeft)
          ((tangent i : Real) + seed.radiusLeft) ∧
      p < mu.real (E.rectSideConnectionEvent 0 seed.radiusLeft
        ((tangent i : Real) - seed.radiusLeft)
        ((tangent i : Real) + seed.radiusLeft)
        (P.shift shift '' (S : Set V))
        (E.rectLeftBoundaryVertices 0 seed.radiusLeft
          ((tangent i : Real) - seed.radiusLeft)
          ((tangent i : Real) + seed.radiusLeft))) := by
  dsimp only
  let base := seed.baseLeft + horizontalShift i.val
  let z := verticalShift (tangent i)
  have hz0 : (z 0 : Real) = 0 := by simp [z]
  have hz1 : (z 1 : Real) = tangent i := by simp [z]
  have himage : P.shift z '' (P.shift base '' (S : Set V)) =
      P.shift (base + verticalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · rintro _ hx
    rw [← himage] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z 0 seed.radiusLeft
      (-(seed.radiusLeft : Real)) seed.radiusLeft u).2 ((seed.left i).1 hu)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have ht := E.rectLeftConnection_translate_measureReal_eq mu hTI z
      0 seed.radiusLeft (-(seed.radiusLeft : Real)) seed.radiusLeft
      (P.shift base '' (S : Set V))
    rw [hz0, hz1, himage] at ht
    have hp := (seed.left i).2
    change p < mu.real (E.rectSideConnectionEvent 0 seed.radiusLeft
      (-(seed.radiusLeft : Real)) seed.radiusLeft
      (P.shift base '' (S : Set V))
      (E.rectLeftBoundaryVertices 0 seed.radiusLeft
        (-(seed.radiusLeft : Real)) seed.radiusLeft)) at hp
    rw [← ht] at hp
    simpa only [base, add_assoc, add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.right_tangential
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (tangent : Fin (margin + 1) → Int) (i : Fin (margin + 1)) :
    let shift := seed.baseRight + horizontalShift (-(i.val : Int)) +
      verticalShift (tangent i)
    P.shift shift '' (S : Set V) ⊆
        E.rectVertices (-(seed.radiusRight : Real)) 0
          ((tangent i : Real) - seed.radiusRight)
          ((tangent i : Real) + seed.radiusRight) ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(seed.radiusRight : Real)) 0
        ((tangent i : Real) - seed.radiusRight)
        ((tangent i : Real) + seed.radiusRight)
        (P.shift shift '' (S : Set V))
        (E.rectRightBoundaryVertices (-(seed.radiusRight : Real)) 0
          ((tangent i : Real) - seed.radiusRight)
          ((tangent i : Real) + seed.radiusRight))) := by
  dsimp only
  let base := seed.baseRight + horizontalShift (-(i.val : Int))
  let z := verticalShift (tangent i)
  have hz0 : (z 0 : Real) = 0 := by simp [z]
  have hz1 : (z 1 : Real) = tangent i := by simp [z]
  have himage : P.shift z '' (P.shift base '' (S : Set V)) =
      P.shift (base + verticalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · rintro _ hx
    rw [← himage] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(seed.radiusRight : Real)) 0
      (-(seed.radiusRight : Real)) seed.radiusRight u).2 ((seed.right i).1 hu)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have ht := E.rectRightConnection_translate_measureReal_eq mu hTI z
      (-(seed.radiusRight : Real)) 0 (-(seed.radiusRight : Real))
      seed.radiusRight (P.shift base '' (S : Set V))
    rw [hz0, hz1, himage] at ht
    have hp := (seed.right i).2
    change p < mu.real (E.rectSideConnectionEvent
      (-(seed.radiusRight : Real)) 0 (-(seed.radiusRight : Real))
      seed.radiusRight (P.shift base '' (S : Set V))
      (E.rectRightBoundaryVertices (-(seed.radiusRight : Real)) 0
        (-(seed.radiusRight : Real)) seed.radiusRight)) at hp
    rw [← ht] at hp
    simpa only [base, add_assoc, add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.bottom_tangential
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (tangent : Fin (margin + 1) → Int) (i : Fin (margin + 1)) :
    let shift := seed.baseBottom + verticalShift i.val +
      horizontalShift (tangent i)
    P.shift shift '' (S : Set V) ⊆
        E.rectVertices ((tangent i : Real) - seed.radiusBottom)
          ((tangent i : Real) + seed.radiusBottom) 0 seed.radiusBottom ∧
      p < mu.real (E.rectSideConnectionEvent
        ((tangent i : Real) - seed.radiusBottom)
        ((tangent i : Real) + seed.radiusBottom) 0 seed.radiusBottom
        (P.shift shift '' (S : Set V))
        (E.rectBottomBoundaryVertices
          ((tangent i : Real) - seed.radiusBottom)
          ((tangent i : Real) + seed.radiusBottom) 0 seed.radiusBottom)) := by
  dsimp only
  let base := seed.baseBottom + verticalShift i.val
  let z := horizontalShift (tangent i)
  have hz0 : (z 0 : Real) = tangent i := by simp [z]
  have hz1 : (z 1 : Real) = 0 := by simp [z]
  have himage : P.shift z '' (P.shift base '' (S : Set V)) =
      P.shift (base + horizontalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · rintro _ hx
    rw [← himage] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(seed.radiusBottom : Real))
      seed.radiusBottom 0 seed.radiusBottom u).2 ((seed.bottom i).1 hu)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have ht := E.rectBottomConnection_translate_measureReal_eq mu hTI z
      (-(seed.radiusBottom : Real)) seed.radiusBottom 0 seed.radiusBottom
      (P.shift base '' (S : Set V))
    rw [hz0, hz1, himage] at ht
    have hp := (seed.bottom i).2
    rw [← ht] at hp
    simpa only [base, add_assoc, add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.top_tangential
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (tangent : Fin (margin + 1) → Int) (i : Fin (margin + 1)) :
    let shift := seed.baseTop + verticalShift (-(i.val : Int)) +
      horizontalShift (tangent i)
    P.shift shift '' (S : Set V) ⊆
        E.rectVertices ((tangent i : Real) - seed.radiusTop)
          ((tangent i : Real) + seed.radiusTop)
          (-(seed.radiusTop : Real)) 0 ∧
      p < mu.real (E.rectSideConnectionEvent
        ((tangent i : Real) - seed.radiusTop)
        ((tangent i : Real) + seed.radiusTop)
        (-(seed.radiusTop : Real)) 0 (P.shift shift '' (S : Set V))
        (E.rectTopBoundaryVertices
          ((tangent i : Real) - seed.radiusTop)
          ((tangent i : Real) + seed.radiusTop)
          (-(seed.radiusTop : Real)) 0)) := by
  dsimp only
  let base := seed.baseTop + verticalShift (-(i.val : Int))
  let z := horizontalShift (tangent i)
  have hz0 : (z 0 : Real) = tangent i := by simp [z]
  have hz1 : (z 1 : Real) = 0 := by simp [z]
  have himage : P.shift z '' (P.shift base '' (S : Set V)) =
      P.shift (base + horizontalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · rintro _ hx
    rw [← himage] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(seed.radiusTop : Real))
      seed.radiusTop (-(seed.radiusTop : Real)) 0 u).2 ((seed.top i).1 hu)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have ht := E.rectTopConnection_translate_measureReal_eq mu hTI z
      (-(seed.radiusTop : Real)) seed.radiusTop (-(seed.radiusTop : Real)) 0
      (P.shift base '' (S : Set V))
    rw [hz0, hz1, himage] at ht
    have hp := (seed.top i).2
    rw [← ht] at hp
    simpa only [base, add_assoc, add_zero, sub_eq_add_neg, add_comm] using hp



theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.left_translate_to_rect
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (i : Fin (margin + 1)) (z : Site 2) (b c d : Real)
    (hb : (seed.radiusLeft : Real) + z 0 ≤ b)
    (hc : c ≤ -(seed.radiusLeft : Real) + z 1)
    (hd : (seed.radiusLeft : Real) + z 1 ≤ d) :
    P.shift z ''
        (P.shift (seed.baseLeft + horizontalShift i.val) '' (S : Set V)) ⊆
          E.rectVertices (z 0) b c d ∧
      p < mu.real (E.rectSideConnectionEvent (z 0) b c d
        (P.shift z ''
          (P.shift (seed.baseLeft + horizontalShift i.val) '' (S : Set V)))
        (E.rectLeftBoundaryVertices (z 0) b c d)) := by
  let source := P.shift (seed.baseLeft + horizontalShift i.val) '' (S : Set V)
  constructor
  · rintro _ ⟨u, hu, rfl⟩
    have hmem := (E.shift_mem_rectVertices z 0 seed.radiusLeft
      (-(seed.radiusLeft : Real)) seed.radiusLeft u).2 ((seed.left i).1 hu)
    exact E.rectVertices_mono (by simp) hb hc hd hmem
  · have ht := E.rectLeftConnection_translate_measureReal_eq mu hTI z
      0 seed.radiusLeft (-(seed.radiusLeft : Real)) seed.radiusLeft source
    have hp := (seed.left i).2
    have hp' : p < mu.real (E.rectSideConnectionEvent (z 0)
        ((seed.radiusLeft : Real) + z 0)
        (-(seed.radiusLeft : Real) + z 1)
        ((seed.radiusLeft : Real) + z 1) (P.shift z '' source)
        (E.rectLeftBoundaryVertices (z 0)
          ((seed.radiusLeft : Real) + z 0)
          (-(seed.radiusLeft : Real) + z 1)
          ((seed.radiusLeft : Real) + z 1))) := by
      have hp0 : p < mu.real (E.rectSideConnectionEvent 0 seed.radiusLeft
          (-(seed.radiusLeft : Real)) seed.radiusLeft source
          (E.rectLeftBoundaryVertices 0 seed.radiusLeft
            (-(seed.radiusLeft : Real)) seed.radiusLeft)) := by
        simpa only [source] using hp
      simpa only [zero_add] using hp0.trans_eq ht.symm
    exact hp'.trans_le (measureReal_mono
      (E.rectLeftConnectionEvent_mono_otherBounds _ hb hc hd))


theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.right_translate_to_rect
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (i : Fin (margin + 1)) (z : Site 2) (a c d : Real)
    (ha : a ≤ -(seed.radiusRight : Real) + z 0)
    (hc : c ≤ -(seed.radiusRight : Real) + z 1)
    (hd : (seed.radiusRight : Real) + z 1 ≤ d) :
    P.shift z '' (P.shift
        (seed.baseRight + horizontalShift (-(i.val : Int))) '' (S : Set V)) ⊆
          E.rectVertices a (z 0) c d ∧
      p < mu.real (E.rectSideConnectionEvent a (z 0) c d
        (P.shift z '' (P.shift
          (seed.baseRight + horizontalShift (-(i.val : Int))) '' (S : Set V)))
        (E.rectRightBoundaryVertices a (z 0) c d)) := by
  let source := P.shift
    (seed.baseRight + horizontalShift (-(i.val : Int))) '' (S : Set V)
  constructor
  · rintro _ ⟨u, hu, rfl⟩
    have hmem := (E.shift_mem_rectVertices z (-(seed.radiusRight : Real)) 0
      (-(seed.radiusRight : Real)) seed.radiusRight u).2 ((seed.right i).1 hu)
    exact E.rectVertices_mono ha (by simp) hc hd hmem
  · have ht := E.rectRightConnection_translate_measureReal_eq mu hTI z
      (-(seed.radiusRight : Real)) 0
      (-(seed.radiusRight : Real)) seed.radiusRight source
    have hp := (seed.right i).2
    have hp' : p < mu.real (E.rectSideConnectionEvent
        (-(seed.radiusRight : Real) + z 0) (z 0)
        (-(seed.radiusRight : Real) + z 1)
        ((seed.radiusRight : Real) + z 1) (P.shift z '' source)
        (E.rectRightBoundaryVertices
          (-(seed.radiusRight : Real) + z 0) (z 0)
          (-(seed.radiusRight : Real) + z 1)
          ((seed.radiusRight : Real) + z 1))) := by
      have hp0 : p < mu.real (E.rectSideConnectionEvent
          (-(seed.radiusRight : Real)) 0 (-(seed.radiusRight : Real))
          seed.radiusRight source (E.rectRightBoundaryVertices
            (-(seed.radiusRight : Real)) 0 (-(seed.radiusRight : Real))
            seed.radiusRight)) := by
        simpa only [source] using hp
      simpa only [zero_add] using hp0.trans_eq ht.symm
    exact hp'.trans_le (measureReal_mono
      (E.rectRightConnectionEvent_mono_otherBounds _ ha hc hd))


theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.bottom_translate_to_rect
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (i : Fin (margin + 1)) (z : Site 2) (a b d : Real)
    (ha : a ≤ -(seed.radiusBottom : Real) + z 0)
    (hb : (seed.radiusBottom : Real) + z 0 ≤ b)
    (hd : (seed.radiusBottom : Real) + z 1 ≤ d) :
    P.shift z ''
        (P.shift (seed.baseBottom + verticalShift i.val) '' (S : Set V)) ⊆
          E.rectVertices a b (z 1) d ∧
      p < mu.real (E.rectSideConnectionEvent a b (z 1) d
        (P.shift z ''
          (P.shift (seed.baseBottom + verticalShift i.val) '' (S : Set V)))
        (E.rectBottomBoundaryVertices a b (z 1) d)) := by
  let source := P.shift (seed.baseBottom + verticalShift i.val) '' (S : Set V)
  constructor
  · rintro _ ⟨u, hu, rfl⟩
    have hmem := (E.shift_mem_rectVertices z (-(seed.radiusBottom : Real))
      seed.radiusBottom 0 seed.radiusBottom u).2 ((seed.bottom i).1 hu)
    exact E.rectVertices_mono ha hb (by simp) hd hmem
  · have ht := E.rectBottomConnection_translate_measureReal_eq mu hTI z
      (-(seed.radiusBottom : Real)) seed.radiusBottom 0 seed.radiusBottom source
    have hp := (seed.bottom i).2
    have hp' : p < mu.real (E.rectSideConnectionEvent
        (-(seed.radiusBottom : Real) + z 0)
        ((seed.radiusBottom : Real) + z 0) (z 1)
        ((seed.radiusBottom : Real) + z 1) (P.shift z '' source)
        (E.rectBottomBoundaryVertices
          (-(seed.radiusBottom : Real) + z 0)
          ((seed.radiusBottom : Real) + z 0) (z 1)
          ((seed.radiusBottom : Real) + z 1))) := by
      have hp0 : p < mu.real (E.rectSideConnectionEvent
          (-(seed.radiusBottom : Real)) seed.radiusBottom 0 seed.radiusBottom
          source (E.rectBottomBoundaryVertices
            (-(seed.radiusBottom : Real)) seed.radiusBottom 0
            seed.radiusBottom)) := by
        simpa only [source] using hp
      simpa only [zero_add] using hp0.trans_eq ht.symm
    exact hp'.trans_le (measureReal_mono
      (E.rectBottomConnectionEvent_mono_otherBounds _ ha hb hd))


theorem PeriodicPlaneEmbedding.NormalBoundaryBandSeed.top_translate_to_rect
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (i : Fin (margin + 1)) (z : Site 2) (a b c : Real)
    (ha : a ≤ -(seed.radiusTop : Real) + z 0)
    (hb : (seed.radiusTop : Real) + z 0 ≤ b)
    (hc : c ≤ -(seed.radiusTop : Real) + z 1) :
    P.shift z '' (P.shift
        (seed.baseTop + verticalShift (-(i.val : Int))) '' (S : Set V)) ⊆
          E.rectVertices a b c (z 1) ∧
      p < mu.real (E.rectSideConnectionEvent a b c (z 1)
        (P.shift z '' (P.shift
          (seed.baseTop + verticalShift (-(i.val : Int))) '' (S : Set V)))
        (E.rectTopBoundaryVertices a b c (z 1))) := by
  let source := P.shift
    (seed.baseTop + verticalShift (-(i.val : Int))) '' (S : Set V)
  constructor
  · rintro _ ⟨u, hu, rfl⟩
    have hmem := (E.shift_mem_rectVertices z (-(seed.radiusTop : Real))
      seed.radiusTop (-(seed.radiusTop : Real)) 0 u).2 ((seed.top i).1 hu)
    exact E.rectVertices_mono ha hb hc (by simp) hmem
  · have ht := E.rectTopConnection_translate_measureReal_eq mu hTI z
      (-(seed.radiusTop : Real)) seed.radiusTop
      (-(seed.radiusTop : Real)) 0 source
    have hp := (seed.top i).2
    have hp' : p < mu.real (E.rectSideConnectionEvent
        (-(seed.radiusTop : Real) + z 0)
        ((seed.radiusTop : Real) + z 0)
        (-(seed.radiusTop : Real) + z 1) (z 1) (P.shift z '' source)
        (E.rectTopBoundaryVertices
          (-(seed.radiusTop : Real) + z 0)
          ((seed.radiusTop : Real) + z 0)
          (-(seed.radiusTop : Real) + z 1) (z 1))) := by
      have hp0 : p < mu.real (E.rectSideConnectionEvent
          (-(seed.radiusTop : Real)) seed.radiusTop
          (-(seed.radiusTop : Real)) 0 source
          (E.rectTopBoundaryVertices (-(seed.radiusTop : Real))
            seed.radiusTop (-(seed.radiusTop : Real)) 0)) := by
        simpa only [source] using hp
      simpa only [zero_add] using hp0.trans_eq ht.symm
    exact hp'.trans_le (measureReal_mono
      (E.rectTopConnectionEvent_mono_otherBounds _ ha hb hc))



theorem PeriodicPlaneEmbedding.exists_orbitBox_normalBoundaryBandSeed
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (N margin : Nat) {delta : Real} (hdelta : 0 < delta) :
    Nonempty (E.NormalBoundaryBandSeed mu (P.orbitBox N) margin
      ((mu.real (P.setHitsInfinite (P.orbitBox N : Set V))) ^ 2 - delta)) := by
  classical
  obtain ⟨baseLeft, hbaseLeft⟩ :=
    E.exists_shift_orbitBox_subset_rightHalfPlane N 0
  obtain ⟨baseRight, hbaseRight⟩ :=
    E.exists_shift_orbitBox_subset_leftComplement N 0
  obtain ⟨baseBottomSwap, hbaseBottom⟩ :=
    E.axisSwap.exists_shift_orbitBox_subset_rightHalfPlane N 0
  obtain ⟨baseTopSwap, hbaseTop⟩ :=
    E.axisSwap.exists_shift_orbitBox_subset_leftComplement N 0
  let baseBottom := siteAxisSwap baseBottomSwap
  let baseTop := siteAxisSwap baseTopSwap
  have hinsideLeft (i : Fin (margin + 1)) :
      P.shift (baseLeft + horizontalShift i.val) ''
          (P.orbitBox N : Set V) ⊆ E.rightHalfPlaneVertices 0 := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseLeft u hu
    change 0 ≤ E.vertexCoord (P.shift baseLeft u) 0 at h
    simp only [E.vertexCoord_shift] at h
    change 0 ≤ E.vertexCoord
      (P.shift (baseLeft + horizontalShift i.val) u) 0
    simp only [P.shift_add, E.vertexCoord_shift]
    simpa using add_nonneg h (show (0 : Real) ≤ i.val by positivity)
  have hinsideRight (i : Fin (margin + 1)) :
      P.shift (baseRight + horizontalShift (-(i.val : Int))) ''
          (P.orbitBox N : Set V) ⊆ {u | E.vertexCoord u 0 ≤ 0} := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseRight u hu
    change ¬ (0 ≤ E.vertexCoord (P.shift baseRight u) 0) at h
    simp only [E.vertexCoord_shift] at h
    change E.vertexCoord
      (P.shift (baseRight + horizontalShift (-(i.val : Int))) u) 0 ≤ 0
    simp only [P.shift_add, E.vertexCoord_shift]
    have hi : (0 : Real) ≤ i.val := by positivity
    simp only [horizontalShift_zero_apply, Int.cast_neg, Int.cast_natCast]
    linarith
  have hinsideBottom (i : Fin (margin + 1)) :
      P.shift (baseBottom + verticalShift i.val) ''
          (P.orbitBox N : Set V) ⊆ {u | 0 ≤ E.vertexCoord u 1} := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseBottom u (by rw [P.axisSwap_orbitBox]; exact hu)
    change 0 ≤ E.axisSwap.vertexCoord
      (P.axisSwap.shift baseBottomSwap u) 0 at h
    have h' : 0 ≤ E.vertexCoord (P.shift baseBottom u) 1 := by
      simpa [baseBottom, PeriodicGraph.axisSwap] using h
    simp only [E.vertexCoord_shift] at h'
    change 0 ≤ E.vertexCoord
      (P.shift (baseBottom + verticalShift i.val) u) 1
    simp only [P.shift_add, E.vertexCoord_shift]
    simpa using add_nonneg h' (show (0 : Real) ≤ i.val by positivity)
  have hinsideTop (i : Fin (margin + 1)) :
      P.shift (baseTop + verticalShift (-(i.val : Int))) ''
          (P.orbitBox N : Set V) ⊆ {u | E.vertexCoord u 1 ≤ 0} := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hbaseTop u (by rw [P.axisSwap_orbitBox]; exact hu)
    change ¬ (0 ≤ E.axisSwap.vertexCoord
      (P.axisSwap.shift baseTopSwap u) 0) at h
    have h' : ¬ (0 ≤ E.vertexCoord (P.shift baseTop u) 1) := by
      simpa [baseTop, PeriodicGraph.axisSwap] using h
    simp only [E.vertexCoord_shift] at h'
    change E.vertexCoord
      (P.shift (baseTop + verticalShift (-(i.val : Int))) u) 1 ≤ 0
    simp only [P.shift_add, E.vertexCoord_shift]
    have hi : (0 : Real) ≤ i.val := by positivity
    simp only [verticalShift_one_apply, Int.cast_neg, Int.cast_natCast]
    linarith
  obtain ⟨radiusLeft, hleft⟩ :=
    E.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) => baseLeft + horizontalShift i.val)
      hinsideLeft hdelta
  obtain ⟨radiusRight, hright⟩ :=
    E.exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) =>
        baseRight + horizontalShift (-(i.val : Int)))
      (by simpa only [neg_zero] using hinsideRight) hdelta
  obtain ⟨radiusBottom, hbottom⟩ :=
    E.exists_translatedFamily_bottomBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) => baseBottom + verticalShift i.val)
      hinsideBottom hdelta
  obtain ⟨radiusTop, htop⟩ :=
    E.exists_translatedFamily_topBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique 0 (P.orbitBox N)
      (fun i : Fin (margin + 1) =>
        baseTop + verticalShift (-(i.val : Int)))
      (by simpa only [neg_zero] using hinsideTop) hdelta
  exact ⟨{
    baseLeft := baseLeft
    baseRight := baseRight
    baseBottom := baseBottom
    baseTop := baseTop
    radiusLeft := radiusLeft
    radiusRight := radiusRight
    radiusBottom := radiusBottom
    radiusTop := radiusTop
    left := by
      simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
        PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent] using hleft
    right := by simpa using hright
    bottom := by simpa using hbottom
    top := by simpa using htop }⟩



structure PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Finset V) (margin M : Nat) (p : Real) where
  zLeft : Site 2
  zRight : Site 2
  zBottom : Site 2
  zTop : Site 2
  left : ∀ i : Fin (margin + 1),
    P.shift (zLeft + horizontalShift i.val) '' (S : Set V) ⊆
        E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        (P.shift (zLeft + horizontalShift i.val) '' (S : Set V))
        (E.rectLeftBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))
  right : ∀ i : Fin (margin + 1),
    P.shift (zRight + horizontalShift (-(i.val : Int))) '' (S : Set V) ⊆
        E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        (P.shift (zRight + horizontalShift (-(i.val : Int))) '' (S : Set V))
        (E.rectRightBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))
  bottom : ∀ i : Fin (margin + 1),
    P.shift (zBottom + verticalShift i.val) '' (S : Set V) ⊆
        E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        (P.shift (zBottom + verticalShift i.val) '' (S : Set V))
        (E.rectBottomBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))
  top : ∀ i : Fin (margin + 1),
    P.shift (zTop + verticalShift (-(i.val : Int))) '' (S : Set V) ⊆
        E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        (P.shift (zTop + verticalShift (-(i.val : Int))) '' (S : Set V))
        (E.rectTopBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))

omit [Countable V] in
theorem PeriodicGraph.normalShift_image_add
    (P : PeriodicGraph V) (S : Set V)
    (base band normal : Site 2) :
    P.shift normal '' (P.shift (base + band) '' S) =
      P.shift (base + normal + band) '' S := by
  rw [Set.image_image]
  apply congrArg (fun f : V → V => f '' S)
  funext x
  rw [← P.shift_add]
  congr 2
  abel


def PeriodicPlaneEmbedding.NormalBoundaryBandSeed.toCommonSquare
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin : Nat} {p : Real}
    (seed : E.NormalBoundaryBandSeed mu S margin p)
    (M : Nat)
    (hleft : seed.radiusLeft ≤ M)
    (hright : seed.radiusRight ≤ M)
    (hbottom : seed.radiusBottom ≤ M)
    (htop : seed.radiusTop ≤ M) :
    E.CommonSquareNormalBoundaryBandData mu S margin M p := by
  let zLeft := seed.baseLeft + horizontalShift (-(M : Int))
  let zRight := seed.baseRight + horizontalShift (M : Int)
  let zBottom := seed.baseBottom + verticalShift (-(M : Int))
  let zTop := seed.baseTop + verticalShift (M : Int)
  refine {
    zLeft := zLeft
    zRight := zRight
    zBottom := zBottom
    zTop := zTop
    left := ?_
    right := ?_
    bottom := ?_
    top := ?_ }
  · intro i
    have hi := E.leftBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusLeft M hleft
      (P.shift (seed.baseLeft + horizontalShift i.val) '' (S : Set V)) p
      (seed.left i).1 (seed.left i).2
    simpa only [zLeft, P.normalShift_image_add] using hi
  · intro i
    have hi := E.rightBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusRight M hright
      (P.shift (seed.baseRight + horizontalShift (-(i.val : Int))) ''
        (S : Set V)) p
      (seed.right i).1 (seed.right i).2
    simpa only [zRight, P.normalShift_image_add] using hi
  · intro i
    have hi := E.bottomBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusBottom M hbottom
      (P.shift (seed.baseBottom + verticalShift i.val) '' (S : Set V)) p
      (seed.bottom i).1 (seed.bottom i).2
    simpa only [zBottom, P.normalShift_image_add] using hi
  · intro i
    have hi := E.topBoundaryExhaustion_to_commonSquare mu hTI
      seed.radiusTop M htop
      (P.shift (seed.baseTop + verticalShift (-(i.val : Int))) ''
        (S : Set V)) p
      (seed.top i).1 (seed.top i).2
    simpa only [zTop, P.normalShift_image_add] using hi



theorem exists_alternating_dominating_sequences (f g : Nat → Nat) :
    ∃ x y : Nat → Nat,
      Tendsto x atTop atTop ∧ Tendsto y atTop atTop ∧
      (∀ n, f (x n) ≤ y n) ∧
      (∀ n, g (y n) ≤ x (n + 1)) := by
  let state : Nat → Nat × Nat := fun n =>
    Nat.rec (0, f 0) (fun k previous =>
      let x := max (k + 1) (g previous.2)
      (x, max (k + 1) (f x))) n
  let x : Nat → Nat := fun n => (state n).1
  let y : Nat → Nat := fun n => (state n).2
  have hxLower (n : Nat) : n ≤ x n := by
    cases n with
    | zero => simp [x, state]
    | succ n => simp [x, state]
  have hyLower (n : Nat) : n ≤ y n := by
    cases n with
    | zero => simp [y, state]
    | succ n => simp [y, state]
  have hxy (n : Nat) : f (x n) ≤ y n := by
    cases n with
    | zero => simp [x, y, state]
    | succ n => simp [x, y, state]
  have hyx (n : Nat) : g (y n) ≤ x (n + 1) := by
    simp [x, y, state]
  refine ⟨x, y, ?_, ?_, hxy, hyx⟩
  · rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (hxLower n)
  · rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (hyLower n)

omit [Countable V] in


theorem normalBand_left_source_aligned
    (baseLeft gridBase : Site 2) (i j : Nat) :
    baseLeft + horizontalShift i +
        (gridBase - baseLeft + verticalShift j) =
      gridBase + horizontalShift i + verticalShift j := by
  abel

omit [Countable V] in

theorem normalBand_right_source_aligned
    (baseRight gridBase : Site 2) (width i j : Nat) :
    baseRight + horizontalShift (-(i : Int)) +
        (gridBase - baseRight + horizontalShift width + verticalShift j) =
      gridBase + horizontalShift ((width : Int) - i) + verticalShift j := by
  funext k
  fin_cases k <;> simp [horizontalShift, verticalShift] <;> omega

omit [Countable V] in

theorem normalBand_bottom_source_aligned
    (baseBottom gridBase : Site 2) (i j : Nat) :
    baseBottom + verticalShift j +
        (gridBase - baseBottom + horizontalShift i) =
      gridBase + horizontalShift i + verticalShift j := by
  abel

omit [Countable V] in

theorem normalBand_top_source_aligned
    (baseTop gridBase : Site 2) (height i j : Nat) :
    baseTop + verticalShift (-(j : Int)) +
        (gridBase - baseTop + verticalShift height + horizontalShift i) =
      gridBase + horizontalShift i + verticalShift ((height : Int) - j) := by
  funext k
  fin_cases k <;> simp [horizontalShift, verticalShift] <;> omega




theorem PeriodicPlaneEmbedding.setHitsInfinite_subset_mixedRectSideConnection_union
    (E : PeriodicPlaneEmbedding P)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Real) (S : Set V)
    (ha : a1 ≤ a0) (hb : b0 ≤ b1) (hc : c0 ≤ c1) (hd : d1 ≤ d0)
    (hS : S ⊆ E.rectVertices a0 b0 c1 d1) :
    P.setHitsInfinite S ⊆
      E.rectSideConnectionEvent a1 b1 c1 d1 S
          (E.rectBottomBoundaryVertices a1 b1 c1 d1) ∪
        (E.rectSideConnectionEvent a1 b1 c1 d1 S
            (E.rectTopBoundaryVertices a1 b1 c1 d1) ∪
          (E.rectSideConnectionEvent a0 b0 c0 d0 S
              (E.rectLeftBoundaryVertices a0 b0 c0 d0) ∪
            E.rectSideConnectionEvent a0 b0 c0 d0 S
              (E.rectRightBoundaryVertices a0 b0 c0 d0))) := by
  intro omega homega
  have hcover := E.setHitsInfinite_subset_rectSideConnection_union
    a0 b0 c1 d1 S hS homega
  rcases hcover with hbottom | htop | hleft | hright
  · exact Or.inl (E.rectBottomConnectionEvent_mono_otherBounds S
      ha hb (le_refl d1) hbottom)
  · exact Or.inr (Or.inl (E.rectTopConnectionEvent_mono_otherBounds S
      ha hb (le_refl c1) htop))
  · exact Or.inr (Or.inr (Or.inl
      (E.rectLeftConnectionEvent_mono_otherBounds S
        (le_refl b0) hc hd hleft)))
  · exact Or.inr (Or.inr (Or.inr
      (E.rectRightConnectionEvent_mono_otherBounds S
        (le_refl a0) hc hd hright)))


theorem PeriodicPlaneEmbedding.preference_mixed_max_add_epsilon_ge_fourthRoot
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Real) (S : Set V)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (ha : a1 ≤ a0) (hb : b0 ≤ b1) (hc : c0 ≤ c1) (hd : d1 ≤ d0)
    (hS : S ⊆ E.rectVertices a0 b0 c1 d1)
    (hBottomTop : mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 S
        (E.rectTopBoundaryVertices a1 b1 c1 d1)) ≤
      mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 S
        (E.rectBottomBoundaryVertices a1 b1 c1 d1)) + epsilon)
    (hLeftRight : mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 S
        (E.rectRightBoundaryVertices a0 b0 c0 d0)) ≤
      mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 S
        (E.rectLeftBoundaryVertices a0 b0 c0 d0)) + epsilon) :
    1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) ≤
      max
        (mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 S
          (E.rectBottomBoundaryVertices a1 b1 c1 d1)))
        (mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 S
          (E.rectLeftBoundaryVertices a0 b0 c0 d0))) + epsilon := by
  let B := E.rectSideConnectionEvent a1 b1 c1 d1 S
    (E.rectBottomBoundaryVertices a1 b1 c1 d1)
  let T := E.rectSideConnectionEvent a1 b1 c1 d1 S
    (E.rectTopBoundaryVertices a1 b1 c1 d1)
  let L := E.rectSideConnectionEvent a0 b0 c0 d0 S
    (E.rectLeftBoundaryVertices a0 b0 c0 d0)
  let R := E.rectSideConnectionEvent a0 b0 c0 d0 S
    (E.rectRightBoundaryVertices a0 b0 c0 d0)
  have hfour := four_event_sqrt_trick mu hFKG
    (E.rectSideConnectionEvent_isIncreasing a1 b1 c1 d1 S
      (E.rectBottomBoundaryVertices a1 b1 c1 d1))
    (E.rectSideConnectionEvent_isIncreasing a1 b1 c1 d1 S
      (E.rectTopBoundaryVertices a1 b1 c1 d1))
    (E.rectSideConnectionEvent_isIncreasing a0 b0 c0 d0 S
      (E.rectLeftBoundaryVertices a0 b0 c0 d0))
    (E.rectSideConnectionEvent_isIncreasing a0 b0 c0 d0 S
      (E.rectRightBoundaryVertices a0 b0 c0 d0))
    (E.rectSideConnectionEvent_measurableSet a1 b1 c1 d1 S
      (E.rectBottomBoundaryVertices a1 b1 c1 d1))
    (E.rectSideConnectionEvent_measurableSet a1 b1 c1 d1 S
      (E.rectTopBoundaryVertices a1 b1 c1 d1))
    (E.rectSideConnectionEvent_measurableSet a0 b0 c0 d0 S
      (E.rectLeftBoundaryVertices a0 b0 c0 d0))
    (E.rectSideConnectionEvent_measurableSet a0 b0 c0 d0 S
      (E.rectRightBoundaryVertices a0 b0 c0 d0))
  have hmass : mu.real (P.setHitsInfinite S) ≤
      mu.real (B ∪ (T ∪ (L ∪ R))) := measureReal_mono
    (E.setHitsInfinite_subset_mixedRectSideConnection_union
      a0 b0 c0 d0 a1 b1 c1 d1 S ha hb hc hd hS)
  have hsqrt : Real.sqrt (Real.sqrt
      (1 - mu.real (B ∪ (T ∪ (L ∪ R))))) ≤
        Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) := by
    gcongr
  have hB : mu.real B ≤ max (mu.real B) (mu.real L) + epsilon :=
    (le_max_left _ _).trans (le_add_of_nonneg_right hepsilon)
  have hL : mu.real L ≤ max (mu.real B) (mu.real L) + epsilon :=
    (le_max_right _ _).trans (le_add_of_nonneg_right hepsilon)
  have hT : mu.real T ≤ max (mu.real B) (mu.real L) + epsilon := by
    dsimp only [B, T, L, R] at hBottomTop ⊢
    linarith [le_max_left (mu.real B) (mu.real L)]
  have hR : mu.real R ≤ max (mu.real B) (mu.real L) + epsilon := by
    dsimp only [B, T, L, R] at hLeftRight ⊢
    linarith [le_max_right (mu.real B) (mu.real L)]
  have hmax : max (max (mu.real B) (mu.real T))
      (max (mu.real L) (mu.real R)) ≤
        max (mu.real B) (mu.real L) + epsilon :=
    max_le (max_le hB hT) (max_le hL hR)
  dsimp only [B, T, L, R] at hfour hsqrt hmax ⊢
  linarith




theorem PeriodicPlaneEmbedding.exists_mixed_approxPreferredSide_crossing_branch
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Real)
    {width height : Nat} (hwidth : 0 < width) (hheight : 0 < height)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (source : PreferenceGridVertex width height → Finset V)
    (bottom top left right : PreferenceGridVertex width height → Real)
    (ha : a1 ≤ a0) (hb : b0 ≤ b1) (hc : c0 ≤ c1) (hd : d1 ≤ d0)
    (hsource : ∀ x, (source x : Set V) ⊆
      E.rectVertices a0 b0 c1 d1)
    (hbottomScore : ∀ x, bottom x = mu.real
      (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V)
        (E.rectBottomBoundaryVertices a1 b1 c1 d1)))
    (htopScore : ∀ x, top x = mu.real
      (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V)
        (E.rectTopBoundaryVertices a1 b1 c1 d1)))
    (hleftScore : ∀ x, left x = mu.real
      (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V)
        (E.rectLeftBoundaryVertices a0 b0 c0 d0)))
    (hrightScore : ∀ x, right x = mu.real
      (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V)
        (E.rectRightBoundaryVertices a0 b0 c0 d0)))
    (hbottom : ∀ i : Fin (width + 1),
      top (i, 0) ≤ bottom (i, 0) + epsilon)
    (htop : ∀ i : Fin (width + 1),
      bottom (i, Fin.last height) ≤ top (i, Fin.last height) + epsilon)
    (hleft : ∀ j : Fin (height + 1),
      right (0, j) ≤ left (0, j) + epsilon)
    (hright : ∀ j : Fin (height + 1),
      left (Fin.last width, j) ≤ right (Fin.last width, j) + epsilon) :
    ∃ x xVertical xHorizontal : PreferenceGridVertex width height,
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧
      ((1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
          bottom x + epsilon ∧
        bottom x *
            (mu.real (P.setHitsInfinite (source xVertical : Set V)) * bottom x -
              mu.real (E.rectanglePairMergeErrorUnion a1 b1 c1 d1
                (source x) (source xVertical)) - epsilon) -
            mu.real (E.rectanglePairMergeErrorUnion a1 b1 c1 d1
              (source x) (source xVertical)) ≤
          mu.real (E.verticalCrossingEvent a1 b1 c1 d1)) ∨
       (1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
          left x + epsilon ∧
        left x *
            (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) * left x -
              mu.real (E.rectanglePairMergeErrorUnion a0 b0 c0 d0
                (source x) (source xHorizontal)) - epsilon) -
            mu.real (E.rectanglePairMergeErrorUnion a0 b0 c0 d0
              (source x) (source xHorizontal)) ≤
          mu.real (E.horizontalCrossingEvent a0 b0 c0 d0))) := by
  obtain ⟨x, xVertical, xHorizontal, hxBottom, hxLeft,
      hxVertical, hxVerticalOpposite, hxHorizontal, hxHorizontalOpposite⟩ :=
    exists_common_weak_approximate_preference_grid_witness
      hwidth hheight epsilon hepsilon bottom top left right
      hbottom htop hleft hright
  have hpref := E.preference_mixed_max_add_epsilon_ge_fourthRoot mu hFKG
    a0 b0 c0 d0 a1 b1 c1 d1 (source x : Set V) epsilon hepsilon
    ha hb hc hd (hsource x)
    (by simpa [hbottomScore x, htopScore x] using hxBottom)
    (by simpa [hleftScore x, hrightScore x] using hxLeft)
  have hpref' :
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
        max (bottom x) (left x) + epsilon := by
    simpa [hbottomScore x, hleftScore x] using hpref
  refine ⟨x, xVertical, xHorizontal, hxVertical, hxHorizontal, ?_⟩
  by_cases hLB : left x ≤ bottom x
  · left
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
        bottom x + epsilon := by simpa [max_eq_left hLB] using hpref'
    have htransfer := E.verticalCrossing_ge_approxPreferredSide_transfer
      mu hFKG a1 b1 c1 d1 (source x) (source xVertical) epsilon
      (by simpa [hbottomScore xVertical, htopScore xVertical] using
        hxVerticalOpposite)
    rw [← hbottomScore x] at htransfer
    exact ⟨hroot, htransfer⟩
  · right
    have hBL : bottom x ≤ left x := le_of_not_ge hLB
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) ≤
        left x + epsilon := by simpa [max_eq_right hBL] using hpref'
    have htransfer := E.horizontalCrossing_ge_approxPreferredSide_transfer
      mu hFKG a0 b0 c0 d0 (source x) (source xHorizontal) epsilon
      (by simpa [hleftScore xHorizontal, hrightScore xHorizontal] using
        hxHorizontalOpposite)
    rw [← hleftScore x] at htransfer
    exact ⟨hroot, htransfer⟩

set_option linter.unusedVariables false in



theorem PeriodicPlaneEmbedding.exists_uniformTemplate_mixedGridPreference_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1)) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n)
      (base : Nat → Site 2)
      (a0 b0 c0 d0 a1 b1 c1 d1 epsilon : Nat → Real)
      (bottom top left right : (n : Nat) →
        PreferenceGridVertex (width n) (height n) → Real),
      Tendsto epsilon atTop (nhds 0) → (∀ n, 0 ≤ epsilon n) →
      (∀ n, a1 n ≤ a0 n) → (∀ n, b0 n ≤ b1 n) →
      (∀ n, c0 n ≤ c1 n) → (∀ n, d1 n ≤ d0 n) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
          E.rectVertices (a0 n) (b0 n) (c1 n) (d1 n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
          E.rectVertices (a0 n) (b0 n) (c0 n) (d0 n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
          E.rectVertices (a1 n) (b1 n) (c1 n) (d1 n)) →
      (∀ n v, bottom n v = mu.real
        (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectBottomBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))) →
      (∀ n v, top n v = mu.real
        (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectTopBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))) →
      (∀ n v, left n v = mu.real
        (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectLeftBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))) →
      (∀ n v, right n v = mu.real
        (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectRightBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))) →
      (∀ n i, top n (i, 0) ≤ bottom n (i, 0) + epsilon n) →
      (∀ n i, bottom n (i, Fin.last (height n)) ≤
        top n (i, Fin.last (height n)) + epsilon n) →
      (∀ n j, right n (0, j) ≤ left n (0, j) + epsilon n) →
      (∀ n j, left n (Fin.last (width n), j) ≤
        right n (Fin.last (width n), j) + epsilon n) →
      Tendsto (fun n => max
        (mu.real (E.horizontalCrossingEvent
          (a0 n) (b0 n) (c0 n) (d0 n)))
        (mu.real (E.verticalCrossingEvent
          (a1 n) (b1 n) (c1 n) (d1 n)))) atTop (nhds 1) := by
  let neighbor : Nat → (Fin 3 × Fin 3) → Finset V := fun n ij =>
    (template n).image (P.shift (preferenceKingOffset ij))
  obtain ⟨radius, _hradius, hmerge⟩ :=
    E.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      mu hTI hunique template neighbor
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight base a0 b0 c0 d0 a1 b1 c1 d1 epsilon
    bottom top left right hepsilon hepsilon0 ha hb hc hd hsource
    hconnector0 hconnector1 hbottomScore htopScore hleftScore hrightScore
    hbottom htop hleft hright
  have hwitness (n : Nat) :=
    E.exists_mixed_approxPreferredSide_crossing_branch mu hFKG
      (a0 n) (b0 n) (c0 n) (d0 n) (a1 n) (b1 n) (c1 n) (d1 n)
      (hwidth n) (hheight n) (epsilon n) (hepsilon0 n)
      (fun v => (template n).image
        (P.shift (base n + preferenceGridSite v)))
      (bottom n) (top n) (left n) (right n)
      (ha n) (hb n) (hc n) (hd n) (hsource n)
      (hbottomScore n) (htopScore n) (hleftScore n) (hrightScore n)
      (hbottom n) (htop n) (hleft n) (hright n)
  choose x xVertical xHorizontal hxVadj hxHadj hbranch using hwitness
  choose ijV hijV using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxVadj n)
  choose ijH hijH using fun n =>
    exists_preferenceKingOffset_of_kingAdj (hxHadj n)
  let source : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Finset V := fun n v =>
    (template n).image (P.shift (base n + preferenceGridSite v))
  let z : Nat → Site 2 := fun n => base n + preferenceGridSite (x n)
  have hzV (n : Nat) : z n + preferenceKingOffset (ijV n) =
      base n + preferenceGridSite (xVertical n) := by
    dsimp only [z]
    rw [hijV n]
    simp only [add_assoc]
  have hzH (n : Nat) : z n + preferenceKingOffset (ijH n) =
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
  have hMv0 := hmerge z ijV a1 b1 c1 d1
    (fun n => hconnector1 n (x n))
  have hMh0 := hmerge z ijH a0 b0 c0 d0
    (fun n => hconnector0 n (x n))
  let Mv : Nat → Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a1 n) (b1 n) (c1 n) (d1 n)
      (source n (x n)) (source n (xVertical n)))
  let Mh : Nat → Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a0 n) (b0 n) (c0 n) (d0 n)
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
        mu.real (E.verticalCrossingEvent
          (a1 n) (b1 n) (c1 n) (d1 n))
  let A : Nat → Real := fun n =>
    if verticalBranch n then bottom n (x n) else left n (x n)
  let Hv : Nat → Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xVertical n) : Set V))
  let Hh : Nat → Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xHorizontal n) : Set V))
  let Cv : Nat → Real := fun n => mu.real
    (E.verticalCrossingEvent (a1 n) (b1 n) (c1 n) (d1 n))
  let Ch : Nat → Real := fun n => mu.real
    (E.horizontalCrossingEvent (a0 n) (b0 n) (c0 n) (d0 n))
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
    · simpa [A, root, source, hv] using ((hbranch n).resolve_left hv).1
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
      have h := (hbranch n).resolve_left hv
      simpa [A, Hh, Ch, Mh, source, hv] using h.2
  simpa [Cv, Ch, max_comm] using
    crossing_max_tendsto_one_of_approxPreferredSide_root_branches
      root A Hv Hh Mv Mh epsilon Cv Ch hroot hrootA hAupper
      hHv hHh hMv hMh hepsilon hcrossingBranch
      (fun _ => measureReal_le_one) (fun _ => measureReal_le_one)

set_option linter.unusedVariables false in


theorem PeriodicPlaneEmbedding.exists_uniformTemplate_mixedBoundaryScores_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1)) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n)
      (base : Nat → Site 2)
      (a0 b0 c0 d0 a1 b1 c1 d1 p : Nat → Real),
      Tendsto p atTop (nhds 1) → (∀ n, p n ≤ 1) →
      (∀ n, a1 n ≤ a0 n) → (∀ n, b0 n ≤ b1 n) →
      (∀ n, c0 n ≤ c1 n) → (∀ n, d1 n ≤ d0 n) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
            E.rectVertices (a0 n) (b0 n) (c1 n) (d1 n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a0 n) (b0 n) (c0 n) (d0 n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a1 n) (b1 n) (c1 n) (d1 n)) →
      (∀ n (i : Fin (width n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n)
          ((template n).image (P.shift (base n + preferenceGridSite
            (i, (0 : Fin (height n + 1))))) : Set V)
          (E.rectBottomBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))) →
      (∀ n (i : Fin (width n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n)
          ((template n).image (P.shift (base n + preferenceGridSite
            (i, Fin.last (height n)))) : Set V)
          (E.rectTopBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))) →
      (∀ n (j : Fin (height n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n)
          ((template n).image (P.shift (base n + preferenceGridSite
            ((0 : Fin (width n + 1)), j))) : Set V)
          (E.rectLeftBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))) →
      (∀ n (j : Fin (height n + 1)), p n ≤ mu.real
        (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n)
          ((template n).image (P.shift (base n + preferenceGridSite
            (Fin.last (width n), j))) : Set V)
          (E.rectRightBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))) →
      Tendsto (fun n => max
        (mu.real (E.horizontalCrossingEvent
          (a0 n) (b0 n) (c0 n) (d0 n)))
        (mu.real (E.verticalCrossingEvent
          (a1 n) (b1 n) (c1 n) (d1 n)))) atTop (nhds 1) := by
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_mixedGridPreference_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight base a0 b0 c0 d0 a1 b1 c1 d1 p
    hplim hp ha hb hc hd hsource hconnector0 hconnector1
    hbottom htop hleft hright
  let epsilon : Nat → Real := fun n => 1 - p n
  let bottom : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v => mu.real (E.rectSideConnectionEvent
      (a1 n) (b1 n) (c1 n) (d1 n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))
  let top : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v => mu.real (E.rectSideConnectionEvent
      (a1 n) (b1 n) (c1 n) (d1 n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))
  let left : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v => mu.real (E.rectSideConnectionEvent
      (a0 n) (b0 n) (c0 n) (d0 n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))
  let right : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real :=
    fun n v => mu.real (E.rectSideConnectionEvent
      (a0 n) (b0 n) (c0 n) (d0 n)
      ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))
  apply hcross width height hwidth hheight base
    a0 b0 c0 d0 a1 b1 c1 d1 epsilon bottom top left right
  · simpa [epsilon] using
      (tendsto_const_nhds (x := (1 : Real))).sub hplim
  · exact fun n => sub_nonneg.mpr (hp n)
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact hsource
  · exact hconnector0
  · exact hconnector1
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n i
    have hTop : top n (i, 0) ≤ 1 := measureReal_le_one
    have hBottom := hbottom n i
    dsimp only [top, bottom, epsilon]
    linarith
  · intro n i
    have hBottom : bottom n (i, Fin.last (height n)) ≤ 1 := measureReal_le_one
    have hTop := htop n i
    dsimp only [top, bottom, epsilon]
    linarith
  · intro n j
    have hRight : right n (0, j) ≤ 1 := measureReal_le_one
    have hLeft := hleft n j
    dsimp only [left, right, epsilon]
    linarith
  · intro n j
    have hLeft : left n (Fin.last (width n), j) ≤ 1 := measureReal_le_one
    have hRight := hright n j
    dsimp only [left, right, epsilon]
    linarith

set_option linter.unusedVariables false in



theorem PeriodicPlaneEmbedding.exists_uniformRadius_boundaryBandScores_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    ∃ radius : Nat → Nat, ∀
      (width height margin : Nat → Nat)
      (base : Nat → Site 2) (a b c d p : Nat → Real),
      (∀ n, 2 * margin n < width n) →
      (∀ n, 2 * margin n < height n) →
      (∀ n, p n ≤ 1) → Tendsto p atTop (nhds 1) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        ((P.orbitBox n).image
          (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        margin n ≤ v.1.val → v.1.val + margin n < width n →
        margin n ≤ v.2.val → v.2.val + margin n < height n →
        (P.shift (base n + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        v.2.val ≤ margin n → p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        height n ≤ v.2.val + margin n → p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        v.1.val ≤ margin n → p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        width n ≤ v.1.val + margin n → p n ≤ mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((P.orbitBox n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) →
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
        (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))))
        atTop (nhds 1) := by
  let template : Nat → Finset V := fun n => P.orbitBox n
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h => h.1
  have htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
      atTop (nhds 1) := by
    simpa only [template, PeriodicGraph.setHitsInfinite,
      PeriodicGraph.orbitBoxHitsInfinite] using
      P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_deepGridPreference_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  refine ⟨radius, ?_⟩
  intro width height margin base a b c d p hwidthSep hheightSep hp hplim
    hsource hconnector hbottom htop hleft hright
  let epsilon : Nat → Real := fun n => 1 - p n
  let bottom : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  let top : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  let left : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  let right : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((P.orbitBox n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))
  let vertical : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Bool := fun n v =>
    boundaryBandPreferenceColor (margin n) (height n) v.2.val
      (epsilon n) (bottom n v) (top n v)
  let horizontal : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Bool := fun n v =>
    boundaryBandPreferenceColor (margin n) (width n) v.1.val
      (epsilon n) (left n v) (right n v)
  have hepsilon : Tendsto epsilon atTop (nhds 0) := by
    simpa [epsilon] using
      (tendsto_const_nhds (x := (1 : Real))).sub hplim
  apply hcross width height margin
    (fun n => (Nat.zero_le (2 * margin n)).trans_lt (hwidthSep n))
    base vertical horizontal
    a b c d epsilon bottom top left right hepsilon
  · exact fun n => sub_nonneg.mpr (hp n)
  · simpa only [template] using hsource
  · exact hconnector
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_true_of_lower hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_false_of_upper
      (hheightSep n) hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_true_of_lower hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_false_of_upper
      (hwidthSep n) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_true_imp
      (sub_nonneg.mpr (hp n)) (hheightSep n) measureReal_le_one
      (fun h => hbottom n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_false_imp
      (sub_nonneg.mpr (hp n)) (hheightSep n) measureReal_le_one
      (fun h => htop n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_true_imp
      (sub_nonneg.mpr (hp n)) (hwidthSep n) measureReal_le_one
      (fun h => hleft n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_false_imp
      (sub_nonneg.mpr (hp n)) (hwidthSep n) measureReal_le_one
      (fun h => hright n v h) (le_refl _) hv

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}




structure PeriodicPlanarDualPair.TwoLevelRectangleArray
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) (B : Real) where
  Bpos : 0 < B
  primalArcBound : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B
  dualArcBound : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B
  a0 : Nat → Real
  b0 : Nat → Real
  c0 : Nat → Real
  d0 : Nat → Real
  a1 : Nat → Real
  b1 : Nat → Real
  c1 : Nat → Real
  d1 : Nat → Real
  spanX0 : ∀ n, a0 n + 5 * B < b0 n - 5 * B
  spanY0 : ∀ n, c0 n + 5 * B < d0 n - 5 * B
  spanX1 : ∀ n, a1 n + 5 * B < b1 n - 5 * B
  spanY1 : ∀ n, c1 n + 5 * B < d1 n - 5 * B
  verticalStart : Tendsto (fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)))
    atTop (nhds 1)
  horizontalEnd : Tendsto (fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B))) atTop (nhds 1)
  primalAdjacent : Tendsto (fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a0 n) (b0 n) (c0 n + 4 * B) (d0 n - 4 * B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (a1 n + 4 * B) (b1 n - 4 * B) (c1 n) (d1 n))))
    atTop (nhds 1)
  dualLevel0 : Tendsto (fun n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n + 4 * B) (d0 n - 4 * B)))) atTop (nhds 1)
  dualLevel1 : Tendsto (fun n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a1 n + 4 * B) (b1 n - 4 * B) (c1 n) (d1 n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B)))) atTop (nhds 1)



theorem PeriodicPlanarDualPair.TwoLevelRectangleArray.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B : Real} (data : D.TwoLevelRectangleArray mu B) : False := by
  let a : Nat → Nat → Real := fun n k => if k = 0 then data.a0 n else data.a1 n
  let b : Nat → Nat → Real := fun n k => if k = 0 then data.b0 n else data.b1 n
  let c : Nat → Nat → Real := fun n k => if k = 0 then data.c0 n else data.c1 n
  let d : Nat → Nat → Real := fun n k => if k = 0 then data.d0 n else data.d1 n
  let K : Nat → Nat := fun _ => 0
  apply D.adjacent_rectangles_contradiction_of_max_limits mu
    (B := B) data.Bpos data.primalArcBound data.dualArcBound a b c d K
  · intro n k
    by_cases hk : k = 0
    · simpa [a, b, hk] using data.spanX0 n
    · simpa [a, b, hk] using data.spanX1 n
  · intro n k
    by_cases hk : k = 0
    · simpa [c, d, hk] using data.spanY0 n
    · simpa [c, d, hk] using data.spanY1 n
  · simpa [a, b, c, d] using data.verticalStart
  · simpa [a, b, c, d, K] using data.horizontalEnd
  · intro k hk
    have hk0 : ∀ n, k n = 0 := by
      intro n
      have := hk n
      dsimp only [K] at this
      omega
    simpa only [a, b, c, d, hk0, if_pos, Nat.zero_add] using
      data.primalAdjacent
  · intro k
    let q0 : Nat → Real := fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (data.a0 n + 4 * B) (data.b0 n - 4 * B)
          (data.c0 n) (data.d0 n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (data.a0 n) (data.b0 n) (data.c0 n + 4 * B)
          (data.d0 n - 4 * B)))
    let q1 : Nat → Real := fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (data.a1 n + 4 * B) (data.b1 n - 4 * B)
          (data.c1 n) (data.d1 n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (data.a1 n) (data.b1 n) (data.c1 n + 4 * B)
          (data.d1 n - 4 * B)))
    let q : Nat → Real := fun n => if k n = 0 then q0 n else q1 n
    have hq0 : Tendsto q0 atTop (nhds 1) := by
      simpa only [q0] using data.dualLevel0
    have hq1 : Tendsto q1 atTop (nhds 1) := by
      simpa only [q1] using data.dualLevel1
    have hlower : ∀ n, min (q0 n) (q1 n) ≤ q n := by
      intro n
      by_cases hn : k n = 0
      · simp [q, hn]
      · simp [q, hn]
    have hupper : ∀ n, q n ≤ 1 := by
      intro n
      by_cases hn : k n = 0
      · simp only [q, hn, if_pos, q0]
        exact max_le measureReal_le_one measureReal_le_one
      · simp only [q, hn, if_neg, q1]
        exact max_le measureReal_le_one measureReal_le_one
    have hq' := (hq0.min hq1).squeeze tendsto_const_nhds hlower
      (fun n => by simpa using hupper n)
    have hq : Tendsto q atTop (nhds 1) := by simpa using hq'
    apply hq.congr'
    filter_upwards with n
    by_cases hn : k n = 0 <;>
      simp [q, q0, q1, a, b, c, d, hn]

end StatMech.FK.PeriodicPlanar
