/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldPairedRecurrence









open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}



theorem exists_carriedAsymmetricEndpointCoordinates_with_radius_requirements
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (B : Nat) (hBpos : 0 < B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (template : Nat -> Finset V)
    (minimumWidth targetY : Nat -> Nat -> Nat)
    (hminimumWidth : forall n radius,
      3 * B + 1 <= minimumWidth n radius)
    (htargetY : forall n radius, 20 * B + 1 <= targetY n radius) :
    exists radius width height : Nat -> Nat,
      Tendsto radius atTop atTop /\
      (forall n, minimumWidth n (radius n) <= width n) /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real
          (P.pairMergeErrorUnion (template (n + 1))
            ((template (n + 1)).image (P.shift
              (preferenceKingOffset (q (n + 1)).2 +
                if (q (n + 1)).1.val = 0 then 0
                else verticalShift (height n))))
            (radius (n + 1)))) atTop (nhds 0)) /\
      Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
        (4 * B) (4 * B + width n) (-4 * B)
          (targetY n (radius n) + 4 * B))) atTop (nhds 1) /\
      Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
        (-4 * B) (width n + 12 * B) (4 * B)
          (4 * B + height n))) atTop (nhds 1) /\
      (forall n, (0 : Real) + 5 * B < width n + 8 * B - 5 * B) /\
      (forall n, -(4 * B : Real) + 5 * B <
        targetY n (radius n) + 4 * B - 5 * B) /\
      (forall n, -(4 * B : Real) + 5 * B <
        width n + 12 * B - 5 * B) /\
      (forall n, (0 : Real) + 5 * B <
        targetY n (radius n) + height n - 5 * B) /\
      (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\
      (forall n, (4 * B : Real) + width n <=
        width n + 8 * B - 4 * B) /\
      (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\
      (forall n, (4 * B : Real) + height n <=
        targetY n (radius n) + height n - 4 * B) := by
  let r : Nat -> Int -> Nat -> Real := fun _ _ _ => 4 * B
  let y : Nat -> Int -> Nat -> Real := fun _ _ _ => 4 * B
  let s : Nat -> Int -> Nat -> Real := fun n _ radius =>
    -(targetY n radius : Real) - 12 * B
  let t : Nat -> Int -> Nat -> Int := fun n _ radius =>
    (3 * targetY n radius + 24 * B : Nat)
  let minimumWidth' : Nat -> Int -> Nat -> Nat := fun n _ radius =>
    minimumWidth n radius
  let minimumHeight : Nat -> Int -> Nat -> Nat := fun _ _ _ => 0
  let horizontalLeft : Nat -> Int -> Nat -> Nat -> Int := fun _ _ _ _ =>
    -(4 * (B : Int))
  let horizontalRight : Nat -> Int -> Nat -> Nat -> Int := fun _ _ _ w =>
    w + 12 * (B : Int)
  have ht (n : Nat) (step : Int) (radius : Nat) :
      3 * (B : Real) < t n step radius := by
    dsimp only [t]
    push_cast
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hy : (20 * B + 1 : Real) <= targetY n radius := by
      exact_mod_cast htargetY n radius
    nlinarith
  have hhorizontalSpan (n : Nat) (step : Int) (radius width : Nat)
      (_hwidth : minimumWidth' n step radius <= width) :
      3 * (B : Real) <
        horizontalRight n step radius width -
          horizontalLeft n step radius width := by
    dsimp only [horizontalRight, horizontalLeft]
    push_cast
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hw : (0 : Real) <= width := by positivity
    nlinarith
  obtain ⟨state, rows, _hstate0, hstateSucc, _hstepNonneg,
      hradius, _hmerge, hmergeShift, hvertical, hhorizontal⟩ :=
    exists_recursiveDependentRadiusFirstAdjacentEndpointRows_with_limits
      E Edual mu muDual hunique hFKGDual hTIDual huniqueDual
      (B : Real) (by positivity) hB template 0 (by omega)
      r y s t ht minimumWidth' minimumHeight horizontalLeft horizontalRight
        hhorizontalSpan
  let radius : Nat -> Nat := fun n => (rows n).radius
  let width : Nat -> Nat := fun n => (rows n).width
  let height : Nat -> Nat := fun n => (rows n).height
  have hstateStep (n : Nat) : (state (n + 1)).1 = (height n : Int) := by
    rw [hstateSucc n]
  have hmergeCarried (q : Nat -> Fin 2 × (Fin 3 × Fin 3)) :
      Tendsto (fun n => mu.real
        (P.pairMergeErrorUnion (template (n + 1))
          ((template (n + 1)).image (P.shift
            (preferenceKingOffset (q (n + 1)).2 +
              if (q (n + 1)).1.val = 0 then 0
              else verticalShift (height n))))
          (radius (n + 1)))) atTop (nhds 0) := by
    apply (hmergeShift q).congr'
    filter_upwards [] with n
    simp only [hstateStep n, radius]
  have hvertical' : Tendsto (fun n => muDual.real
      (Edual.verticalCrossingEvent (4 * B) (4 * B + width n)
        (-4 * B) (targetY n (radius n) + 4 * B))) atTop (nhds 1) := by
    apply hvertical.congr'
    filter_upwards [] with n
    congr 2 <;> dsimp only [r, s, t, width] <;> push_cast <;> ring
  have hhorizontal' : Tendsto (fun n => muDual.real
      (Edual.horizontalCrossingEvent (-4 * B) (width n + 12 * B)
        (4 * B) (4 * B + height n))) atTop (nhds 1) := by
    apply hhorizontal.congr'
    filter_upwards [] with n
    congr 2 <;>
      dsimp only [horizontalLeft, horizontalRight, y, width, height] <;>
      push_cast <;> ring
  have hwidthLower (n : Nat) : minimumWidth n (radius n) <= width n :=
    (rows n).minimumWidth_le
  refine ⟨radius, width, height, hradius, hwidthLower, hmergeCarried,
    hvertical', hhorizontal', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have hw0 : 3 * B + 1 <= width n :=
      (hminimumWidth n (radius n)).trans (hwidthLower n)
    have hw : (3 * B + 1 : Real) <= width n := by exact_mod_cast hw0
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    norm_num at hw ⊢
    linarith
  · intro n
    have hy : (20 * B + 1 : Real) <= targetY n (radius n) := by
      exact_mod_cast htargetY n (radius n)
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    push_cast
    nlinarith
  · intro n
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hw : (0 : Real) <= width n := by positivity
    push_cast
    linarith
  · intro n
    have hy : (20 * B + 1 : Real) <= targetY n (radius n) := by
      exact_mod_cast htargetY n (radius n)
    have hBreal : (0 : Real) < B := by exact_mod_cast hBpos
    have hh : (0 : Real) <= height n := by positivity
    push_cast
    nlinarith
  · intro n
    norm_num
  · intro n
    have hBreal : (0 : Real) <= B := by positivity
    push_cast
    linarith
  · intro n
    norm_num
  · intro n
    have hy : (20 * B + 1 : Real) <= targetY n (radius n) := by
      exact_mod_cast htargetY n (radius n)
    push_cast
    linarith



theorem exists_carriedAsymmetricEndpointCoordinates_with_requirements
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (B : Nat) (hBpos : 0 < B)
    (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
    (template : Nat -> Finset V)
    (minimumWidth targetY : Nat -> Nat)
    (hminimumWidth : forall n, 3 * B + 1 <= minimumWidth n)
    (htargetY : forall n, 20 * B + 1 <= targetY n) :
    exists radius width height : Nat -> Nat,
      Tendsto radius atTop atTop /\
      (forall n, minimumWidth n <= width n) /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real
          (P.pairMergeErrorUnion (template (n + 1))
            ((template (n + 1)).image (P.shift
              (preferenceKingOffset (q (n + 1)).2 +
                if (q (n + 1)).1.val = 0 then 0
                else verticalShift (height n))))
            (radius (n + 1)))) atTop (nhds 0)) /\
      Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
        (4 * B) (4 * B + width n) (-4 * B)
          (targetY n + 4 * B))) atTop (nhds 1) /\
      Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
        (-4 * B) (width n + 12 * B) (4 * B)
          (4 * B + height n))) atTop (nhds 1) /\
      (forall n, (0 : Real) + 5 * B < width n + 8 * B - 5 * B) /\
      (forall n, -(4 * B : Real) + 5 * B <
        targetY n + 4 * B - 5 * B) /\
      (forall n, -(4 * B : Real) + 5 * B <
        width n + 12 * B - 5 * B) /\
      (forall n, (0 : Real) + 5 * B <
        targetY n + height n - 5 * B) /\
      (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\
      (forall n, (4 * B : Real) + width n <=
        width n + 8 * B - 4 * B) /\
      (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\
      (forall n, (4 * B : Real) + height n <=
        targetY n + height n - 4 * B) := by
  simpa using
    (exists_carriedAsymmetricEndpointCoordinates_with_radius_requirements
      E Edual mu muDual hunique hFKGDual hTIDual huniqueDual B hBpos hB
      template (fun n _ => minimumWidth n) (fun n _ => targetY n)
      (fun n _ => hminimumWidth n) (fun n _ => htargetY n))



theorem PeriodicPlanarDualPair.exists_carriedAsymmetricEndpoints_false_of_primal_limit_with_requirements
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG (D.dualMeasure mu))
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (huniqueDual : (D.dualMeasure mu)
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (B : Nat) (hBpos : 0 < B)
    (hBp : forall {x z : V} (hxz : P.graph.Adj x z)
      (u) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxz u - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x z : W} (hxz : Pdual.graph.Adj x z)
      (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxz u - D.dualEmbedding.vertex x) i| <= B)
    (template : Nat -> Finset V)
    (minimumWidth targetY : Nat -> Nat)
    (hminimumWidth : forall n, 3 * B + 1 <= minimumWidth n)
    (htargetY : forall n, 20 * B + 1 <= targetY n) :
    exists radius width height : Nat -> Nat,
      Tendsto radius atTop atTop /\
      (forall n, minimumWidth n <= width n) /\
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real
          (P.pairMergeErrorUnion (template (n + 1))
            ((template (n + 1)).image (P.shift
              (preferenceKingOffset (q (n + 1)).2 +
                if (q (n + 1)).1.val = 0 then 0
                else verticalShift (height n))))
            (radius (n + 1)))) atTop (nhds 0)) /\
      (Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          0 (width n + 8 * B) 0 (targetY n)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          0 (width n + 8 * B) 0 (targetY n + height n))))
        atTop (nhds 1) -> False) := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  obtain ⟨radius, width, height, hradius, hwidth, hmerge,
      hdualV0, hdualH0, hspanHX, hspanDVY, hspanDHX, hspanVY,
      hDVLeft, hDVRight, hDHBottom, hDHTop⟩ :=
    exists_carriedAsymmetricEndpointCoordinates_with_requirements
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      hunique hFKGDual hTIDual huniqueDual B hBpos hBd template
      minimumWidth targetY hminimumWidth htargetY
  have hdualV : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (4 * B) (4 * B + width n) (-4 * B)
          (targetY n + 4 * B))) atTop (nhds 1) := by
    apply hdualV0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
  have hdualH : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (-4 * B) (width n + 12 * B) (4 * B)
          (4 * B + height n))) atTop (nhds 1) := by
    apply hdualH0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
  have hspanDVY' : forall n,
      -(4 * B : Real) + 5 * B <
        (targetY n : Real) + 4 * B - 5 * B := by
    simpa using hspanDVY
  have hspanVY' : forall n,
      (0 : Real) + 5 * B <
        (targetY n : Real) + height n - 5 * B := by
    simpa using hspanVY
  have hDHTop' : forall n,
      (4 * B : Real) + height n <=
        (targetY n : Real) + height n - 4 * B := by
    simpa using hDHTop
  refine ⟨radius, width, height, hradius, hwidth, hmerge, ?_⟩
  intro hprimal
  exact D.fullyAsymmetricEndpointCoordinates_false mu (B : Real)
    (by exact_mod_cast hBpos) hBp hBd
    (fun _ => 0) (fun n => width n + 8 * B)
    (fun _ => 0) (fun n => (targetY n : Real))
    (fun _ => 0) (fun n => width n + 8 * B)
    (fun _ => 0) (fun n => (targetY n : Real) + height n)
    (fun _ => 4 * B) (fun n => 4 * B + width n)
    (fun _ => -4 * B) (fun n => targetY n + 4 * B)
    (fun _ => -4 * B) (fun n => width n + 12 * B)
    (fun _ => 4 * B) (fun n => 4 * B + height n)
    hspanHX (fun n => by nlinarith [hspanDVY' n])
    (fun n => by nlinarith [hspanDHX n]) hspanVY'
    (fun _ => by norm_num) (fun _ => by norm_num)
    hDVLeft hDVRight
    (fun _ => by norm_num) (fun _ => by apply le_of_eq; ring)
    hDHBottom hDHTop' hprimal hdualV hdualH




theorem PeriodicPlaneEmbedding.centeredCrossingMax_tendsto_origin
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (M outerWidth outerHeight step : Nat -> Nat)
    (hwidth : forall n, 2 * M n <= outerWidth n)
    (hheight : forall n, 2 * M n <= outerHeight n)
    (hcentered : Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (-(M n : Real))
        (M n + (outerWidth n - 2 * M n) : Nat)
        (-(M n : Real))
        (M n + (outerHeight n - 2 * M n) : Nat)))
      (mu.real (E.verticalCrossingEvent
        (-(M n : Real))
        (M n + (outerWidth n - 2 * M n) : Nat)
        (-(M n : Real))
        ((M n + (outerHeight n - 2 * M n) : Nat) + step n))))
      atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        0 (outerWidth n) 0 (outerHeight n)))
      (mu.real (E.verticalCrossingEvent
        0 (outerWidth n) 0 (outerHeight n + step n))))
      atTop (nhds 1) := by
  let z : Nat -> Site 2 := fun n => ![(M n : Int), (M n : Int)]
  have htranslated := E.crossingMax_independent_translate_tendsto_one
    mu hTI z z
    (fun n => -(M n : Real))
    (fun n => (M n + (outerWidth n - 2 * M n) : Nat))
    (fun n => -(M n : Real))
    (fun n => (M n + (outerHeight n - 2 * M n) : Nat))
    (fun n => -(M n : Real))
    (fun n => (M n + (outerWidth n - 2 * M n) : Nat))
    (fun n => -(M n : Real))
    (fun n => ((M n + (outerHeight n - 2 * M n) : Nat) + step n))
    hcentered
  apply htranslated.congr'
  filter_upwards [] with n
  have hwn := hwidth n
  have hhn := hheight n
  congr 3 <;> simp [z]
  all_goals first | rw [Nat.cast_sub hwn] | rw [Nat.cast_sub hhn]
  all_goals push_cast <;> ring




theorem PeriodicPlaneEmbedding.adjacentCrossingMax_tendsto_one_mono_vertical_width
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (a b c d step aVertical bVertical : Nat -> Real)
    (ha : forall n, aVertical n <= a n)
    (hb : forall n, b n <= bVertical n)
    (hlimit : Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (a n) (b n) (c n) (d n)))
      (mu.real (E.verticalCrossingEvent
        (a n) (b n) (c n) (d n + step n)))) atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (a n) (b n) (c n) (d n)))
      (mu.real (E.verticalCrossingEvent
        (aVertical n) (bVertical n) (c n) (d n + step n))))
      atTop (nhds 1) := by
  exact hlimit.squeeze tendsto_const_nhds
    (fun n => max_le_max (le_refl _)
      (measureReal_mono
        (E.verticalCrossingEvent_mono_horizontal (ha n) (hb n))))
    (fun _ => max_le measureReal_le_one measureReal_le_one)





theorem PeriodicPlanarDualPair.pointwiseRecursiveRectangleArray_false_of_primal_dualMeasure_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a b c d : Nat -> Nat -> Real)
    (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
    (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
    (hverticalStart : Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (a 0 n + 4 * B) (b 0 n - 4 * B) (c 0 n) (d 0 n)))
      atTop (nhds 1))
    (hhorizontalLevel : forall k, Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (a (k + 1) n) (b (k + 1) n)
        (c (k + 1) n + 4 * B) (d (k + 1) n - 4 * B)))
      atTop (nhds 1))
    (hnormalAdjacent : forall k, Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a (k + 1) n + 4 * B) (b (k + 1) n - 4 * B)
        (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
    (hdualLevel : forall k, Tendsto (fun n => max
      ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
        (a k n + 4 * B) (b k n - 4 * B) (c k n) (d k n)))
      ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
        (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B))))
      atTop (nhds 1)) : False := by
  apply D.pointwiseRecursiveRectangleArray_false_of_normal_rotated_limits
    mu B hBpos hBp hBd a b c d hspanX hspanY hverticalStart
    hhorizontalLevel hnormalAdjacent
  intro k
  exact D.dualMeasure_crossingMax_tendsto_one mu
    (fun n => a k n + 4 * B) (fun n => b k n - 4 * B)
    (c k) (d k) (a k) (b k)
    (fun n => c k n + 4 * B) (fun n => d k n - 4 * B)
    (hdualLevel k)






structure PeriodicPlanarDualPair.EndpointBridgedRectangleArrayCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  B : Real
  Bpos : 0 < B
  primalArcBound : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B
  dualArcBound : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B
  startA : Nat -> Real
  startB : Nat -> Real
  startC : Nat -> Real
  startD : Nat -> Real
  lowerA : Nat -> Real
  lowerB : Nat -> Real
  lowerC : Nat -> Real
  lowerD : Nat -> Real
  upperA : Nat -> Real
  upperB : Nat -> Real
  upperC : Nat -> Real
  upperD : Nat -> Real
  endA : Nat -> Real
  endB : Nat -> Real
  endC : Nat -> Real
  endD : Nat -> Real
  startSpanX : forall n, startA n + 5 * B < startB n - 5 * B
  startSpanY : forall n, startC n + 5 * B < startD n - 5 * B
  lowerSpanX : forall n, lowerA n + 5 * B < lowerB n - 5 * B
  lowerSpanY : forall n, lowerC n + 5 * B < lowerD n - 5 * B
  upperSpanX : forall n, upperA n + 5 * B < upperB n - 5 * B
  upperSpanY : forall n, upperC n + 5 * B < upperD n - 5 * B
  endSpanX : forall n, endA n + 5 * B < endB n - 5 * B
  endSpanY : forall n, endC n + 5 * B < endD n - 5 * B
  verticalStart : Tendsto (fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (startA n + 4 * B) (startB n - 4 * B) (startC n) (startD n)))
    atTop (nhds 1)
  horizontalEnd : Tendsto (fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (endA n) (endB n) (endC n + 4 * B) (endD n - 4 * B)))
    atTop (nhds 1)
  startBridge : Tendsto (fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (startA n) (startB n) (startC n + 4 * B) (startD n - 4 * B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (lowerA n + 4 * B) (lowerB n - 4 * B) (lowerC n) (lowerD n))))
    atTop (nhds 1)
  coreAdjacent : Tendsto (fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (lowerA n) (lowerB n) (lowerC n + 4 * B) (lowerD n - 4 * B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (upperA n + 4 * B) (upperB n - 4 * B) (upperC n) (upperD n))))
    atTop (nhds 1)
  endBridge : Tendsto (fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (upperA n) (upperB n) (upperC n + 4 * B) (upperD n - 4 * B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (endA n + 4 * B) (endB n - 4 * B) (endC n) (endD n))))
    atTop (nhds 1)
  dualStart : Tendsto (fun n => max
    ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
      (startA n + 4 * B) (startB n - 4 * B) (startC n) (startD n)))
    ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
      (startA n) (startB n) (startC n + 4 * B) (startD n - 4 * B))))
    atTop (nhds 1)
  dualLower : Tendsto (fun n => max
    ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
      (lowerA n + 4 * B) (lowerB n - 4 * B) (lowerC n) (lowerD n)))
    ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
      (lowerA n) (lowerB n) (lowerC n + 4 * B) (lowerD n - 4 * B))))
    atTop (nhds 1)
  dualUpper : Tendsto (fun n => max
    ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
      (upperA n + 4 * B) (upperB n - 4 * B) (upperC n) (upperD n)))
    ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
      (upperA n) (upperB n) (upperC n + 4 * B) (upperD n - 4 * B))))
    atTop (nhds 1)
  dualEnd : Tendsto (fun n => max
    ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
      (endA n + 4 * B) (endB n - 4 * B) (endC n) (endD n)))
    ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
      (endA n) (endB n) (endC n + 4 * B) (endD n - 4 * B))))
    atTop (nhds 1)



theorem PeriodicPlanarDualPair.EndpointBridgedRectangleArrayCertificate.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (data : D.EndpointBridgedRectangleArrayCertificate mu) : False := by
  let a : Nat -> Nat -> Real := fun n k =>
    if k = 0 then data.startA n else if k = 1 then data.lowerA n
    else if k = 2 then data.upperA n else data.endA n
  let b : Nat -> Nat -> Real := fun n k =>
    if k = 0 then data.startB n else if k = 1 then data.lowerB n
    else if k = 2 then data.upperB n else data.endB n
  let c : Nat -> Nat -> Real := fun n k =>
    if k = 0 then data.startC n else if k = 1 then data.lowerC n
    else if k = 2 then data.upperC n else data.endC n
  let d : Nat -> Nat -> Real := fun n k =>
    if k = 0 then data.startD n else if k = 1 then data.lowerD n
    else if k = 2 then data.upperD n else data.endD n
  let K : Nat -> Nat := fun _ => 2
  let primal0 : Nat -> Real := fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (data.startA n) (data.startB n)
      (data.startC n + 4 * data.B) (data.startD n - 4 * data.B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (data.lowerA n + 4 * data.B) (data.lowerB n - 4 * data.B)
      (data.lowerC n) (data.lowerD n)))
  let primal1 : Nat -> Real := fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (data.lowerA n) (data.lowerB n)
      (data.lowerC n + 4 * data.B) (data.lowerD n - 4 * data.B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (data.upperA n + 4 * data.B) (data.upperB n - 4 * data.B)
      (data.upperC n) (data.upperD n)))
  let primal2 : Nat -> Real := fun n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (data.upperA n) (data.upperB n)
      (data.upperC n + 4 * data.B) (data.upperD n - 4 * data.B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (data.endA n + 4 * data.B) (data.endB n - 4 * data.B)
      (data.endC n) (data.endD n)))
  have hprimalMin : Tendsto (fun n =>
      min (primal0 n) (min (primal1 n) (primal2 n))) atTop (nhds 1) := by
    simpa only [primal0, primal1, primal2, min_self] using
      data.startBridge.min (data.coreAdjacent.min data.endBridge)
  have hdual0 := D.dualMeasure_crossingMax_tendsto_one mu
    (fun n => data.startA n + 4 * data.B)
    (fun n => data.startB n - 4 * data.B) data.startC data.startD
    data.startA data.startB
    (fun n => data.startC n + 4 * data.B)
    (fun n => data.startD n - 4 * data.B) data.dualStart
  have hdual1 := D.dualMeasure_crossingMax_tendsto_one mu
    (fun n => data.lowerA n + 4 * data.B)
    (fun n => data.lowerB n - 4 * data.B) data.lowerC data.lowerD
    data.lowerA data.lowerB
    (fun n => data.lowerC n + 4 * data.B)
    (fun n => data.lowerD n - 4 * data.B) data.dualLower
  have hdual2 := D.dualMeasure_crossingMax_tendsto_one mu
    (fun n => data.upperA n + 4 * data.B)
    (fun n => data.upperB n - 4 * data.B) data.upperC data.upperD
    data.upperA data.upperB
    (fun n => data.upperC n + 4 * data.B)
    (fun n => data.upperD n - 4 * data.B) data.dualUpper
  have hdual3 := D.dualMeasure_crossingMax_tendsto_one mu
    (fun n => data.endA n + 4 * data.B)
    (fun n => data.endB n - 4 * data.B) data.endC data.endD
    data.endA data.endB
    (fun n => data.endC n + 4 * data.B)
    (fun n => data.endD n - 4 * data.B) data.dualEnd
  let dual0 : Nat -> Real := fun n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (data.startA n + 4 * data.B) (data.startB n - 4 * data.B)
        (data.startC n) (data.startD n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (data.startA n) (data.startB n)
        (data.startC n + 4 * data.B) (data.startD n - 4 * data.B)))
  let dual1 : Nat -> Real := fun n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (data.lowerA n + 4 * data.B) (data.lowerB n - 4 * data.B)
        (data.lowerC n) (data.lowerD n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (data.lowerA n) (data.lowerB n)
        (data.lowerC n + 4 * data.B) (data.lowerD n - 4 * data.B)))
  let dual2 : Nat -> Real := fun n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (data.upperA n + 4 * data.B) (data.upperB n - 4 * data.B)
        (data.upperC n) (data.upperD n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (data.upperA n) (data.upperB n)
        (data.upperC n + 4 * data.B) (data.upperD n - 4 * data.B)))
  let dual3 : Nat -> Real := fun n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (data.endA n + 4 * data.B) (data.endB n - 4 * data.B)
        (data.endC n) (data.endD n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (data.endA n) (data.endB n)
        (data.endC n + 4 * data.B) (data.endD n - 4 * data.B)))
  have hdualMin : Tendsto (fun n => min (dual0 n)
      (min (dual1 n) (min (dual2 n) (dual3 n)))) atTop (nhds 1) := by
    simpa only [dual0, dual1, dual2, dual3, min_self] using
      hdual0.min (hdual1.min (hdual2.min hdual3))
  apply PeriodicPlanarDualPair.RecursiveRectangleArrayCertificate.false D mu {
    B := data.B
    Bpos := data.Bpos
    primalArcBound := data.primalArcBound
    dualArcBound := data.dualArcBound
    a := a
    b := b
    c := c
    d := d
    K := K
    spanX := ?_
    spanY := ?_
    verticalStart := ?_
    horizontalEnd := ?_
    primalAdjacent := ?_
    dualLevels := ?_ }
  · intro n k
    by_cases hk0 : k = 0
    · simpa only [a, b, hk0, if_pos] using data.startSpanX n
    by_cases hk1 : k = 1
    · simp only [a, b, hk0, if_neg, hk1, if_pos]
      exact data.lowerSpanX n
    by_cases hk2 : k = 2
    · simp only [a, b, hk0, if_neg, hk1, hk2, if_pos]
      exact data.upperSpanX n
    · simp only [a, b, hk0, if_neg, hk1, hk2]
      exact data.endSpanX n
  · intro n k
    by_cases hk0 : k = 0
    · simpa only [c, d, hk0, if_pos] using data.startSpanY n
    by_cases hk1 : k = 1
    · simp only [c, d, hk0, if_neg, hk1, if_pos]
      exact data.lowerSpanY n
    by_cases hk2 : k = 2
    · simp only [c, d, hk0, if_neg, hk1, hk2, if_pos]
      exact data.upperSpanY n
    · simp only [c, d, hk0, if_neg, hk1, hk2]
      exact data.endSpanY n
  · simpa only [a, b, c, d, if_pos] using data.verticalStart
  · simpa [K, a, b, c, d] using data.horizontalEnd
  · intro k hk
    apply hprimalMin.squeeze tendsto_const_nhds
    · intro n
      have hcases : k n = 0 ∨ k n = 1 ∨ k n = 2 := by
        have := hk n
        dsimp only [K] at this
        omega
      rcases hcases with h0 | h1 | h2
      · simpa only [a, b, c, d, h0, if_pos, Nat.zero_add, if_false,
          one_ne_zero, primal0] using
          (min_le_left (primal0 n) (min (primal1 n) (primal2 n)))
      · have h10 : k n ≠ 0 := by omega
        simpa only [a, b, c, d, h1, h10, if_false, if_pos,
            Nat.reduceAdd, OfNat.ofNat, one_ne_zero, primal1] using
          ((min_le_right (primal0 n) (min (primal1 n) (primal2 n))).trans
            (min_le_left (primal1 n) (primal2 n)))
      · have h20 : k n ≠ 0 := by omega
        have h21 : k n ≠ 1 := by omega
        simpa only [a, b, c, d, h2, h20, h21, if_false, if_pos,
            Nat.reduceAdd, OfNat.ofNat, one_ne_zero, primal2] using
          ((min_le_right (primal0 n) (min (primal1 n) (primal2 n))).trans
            (min_le_right (primal1 n) (primal2 n)))
    · intro n
      exact max_le measureReal_le_one measureReal_le_one
  · intro k hk
    apply hdualMin.squeeze tendsto_const_nhds
    · intro n
      have hcases : k n = 0 ∨ k n = 1 ∨ k n = 2 ∨ k n = 3 := by
        have := hk n
        dsimp only [K] at this
        omega
      rcases hcases with h0 | h1 | h2 | h3
      · simpa only [a, b, c, d, h0, if_pos, dual0] using
          (min_le_left (dual0 n)
            (min (dual1 n) (min (dual2 n) (dual3 n))))
      · have h10 : k n ≠ 0 := by omega
        simpa only [a, b, c, d, h1, h10, if_false, if_pos, dual1] using
          ((min_le_right (dual0 n)
            (min (dual1 n) (min (dual2 n) (dual3 n)))).trans
              (min_le_left (dual1 n) (min (dual2 n) (dual3 n))))
      · have h20 : k n ≠ 0 := by omega
        have h21 : k n ≠ 1 := by omega
        simpa only [a, b, c, d, h2, h20, h21, if_false, if_pos, dual2] using
          ((min_le_right (dual0 n)
            (min (dual1 n) (min (dual2 n) (dual3 n)))).trans
              ((min_le_right (dual1 n) (min (dual2 n) (dual3 n))).trans
                (min_le_left (dual2 n) (dual3 n))))
      · have h30 : k n ≠ 0 := by omega
        have h31 : k n ≠ 1 := by omega
        have h32 : k n ≠ 2 := by omega
        simpa only [a, b, c, d, h3, h30, h31, h32, if_false, dual3] using
          ((min_le_right (dual0 n)
            (min (dual1 n) (min (dual2 n) (dual3 n)))).trans
              ((min_le_right (dual1 n) (min (dual2 n) (dual3 n))).trans
                (min_le_right (dual2 n) (dual3 n))))
    · intro n
      exact max_le measureReal_le_one measureReal_le_one



theorem PeriodicPlaneEmbedding.verticalEndpoint_tendsto_startBridge_of_mono
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (startA startB startC startD lowerA lowerB : Nat -> Real)
    (hlowerA : forall n, lowerA n <= startA n)
    (hlowerB : forall n, startB n <= lowerB n)
    (hvertical : Tendsto (fun n => mu.real (E.verticalCrossingEvent
      (startA n + 4 * B) (startB n - 4 * B)
      (startC n) (startD n))) atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (startA n) (startB n)
        (startC n + 4 * B) (startD n - 4 * B)))
      (mu.real (E.verticalCrossingEvent
        (lowerA n + 4 * B) (lowerB n - 4 * B)
        (startC n) (startD n)))) atTop (nhds 1) := by
  have hwide := E.verticalCrossing_tendsto_one_mono_horizontal mu
    (fun n => startA n + 4 * B) (fun n => startB n - 4 * B)
    startC startD (fun n => lowerA n + 4 * B)
    (fun n => lowerB n - 4 * B)
    (fun n => by linarith [hlowerA n])
    (fun n => by linarith [hlowerB n]) hvertical
  exact hwide.squeeze tendsto_const_nhds
    (fun _ => le_max_right _ _) (fun _ => max_le measureReal_le_one measureReal_le_one)



theorem PeriodicPlaneEmbedding.horizontalEndpoint_tendsto_endBridge_of_mono
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (endA endB upperC upperD endC endD : Nat -> Real)
    (hupperC : forall n, upperC n <= endC n)
    (hupperD : forall n, endD n <= upperD n)
    (hhorizontal : Tendsto (fun n => mu.real (E.horizontalCrossingEvent
      (endA n) (endB n) (endC n + 4 * B) (endD n - 4 * B)))
      atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (endA n) (endB n)
        (upperC n + 4 * B) (upperD n - 4 * B)))
      (mu.real (E.verticalCrossingEvent
        (endA n + 4 * B) (endB n - 4 * B)
        (endC n) (endD n)))) atTop (nhds 1) := by
  have htall := E.horizontalCrossing_tendsto_one_mono_vertical mu
    endA endB (fun n => endC n + 4 * B) (fun n => endD n - 4 * B)
    (fun n => upperC n + 4 * B) (fun n => upperD n - 4 * B)
    (fun n => by linarith [hupperC n])
    (fun n => by linarith [hupperD n]) hhorizontal
  exact htall.squeeze tendsto_const_nhds
    (fun _ => le_max_left _ _) (fun _ => max_le measureReal_le_one measureReal_le_one)




theorem PeriodicGraph.exists_finiteAdjacentHeights_pairMergeRadius_at_error
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Finset V) (steps : Finset Int) (cutoff : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists radius : Nat, cutoff <= radius /\
      forall step, step ∈ steps -> forall q : Fin 2 × (Fin 3 × Fin 3),
        mu.real (P.pairMergeErrorUnion template
          (template.image (P.shift (preferenceKingOffset q.2 +
            if q.1.val = 0 then 0 else verticalShift step))) radius) <
          epsilon := by
  classical
  let Branch := {step // step ∈ steps} × (Fin 2 × (Fin 3 × Fin 3))
  let neighbor : Nat -> Branch -> Finset V := fun _ branch =>
    template.image (P.shift (preferenceKingOffset branch.2.2 +
      if branch.2.1.val = 0 then 0 else verticalShift branch.1.1))
  obtain ⟨radius, hradius⟩ := P.exists_uniform_pairMergeRadius mu hunique
    (fun _ => template) neighbor
  have heventually : ∀ᶠ n : Nat in atTop,
      (1 : Real) / (n + 1) < epsilon :=
    (tendsto_order.1 tendsto_one_div_add_atTop_nhds_zero_nat).2
      epsilon hepsilon
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 heventually
  let n := max cutoff threshold
  refine ⟨radius n, (Nat.le_max_left _ _).trans (hradius n).1, ?_⟩
  intro step hstep q
  let branch : Branch := (⟨step, hstep⟩, q)
  exact ((hradius n).2 branch).trans
    (hthreshold n (Nat.le_max_right _ _))





theorem PeriodicPlaneEmbedding.exists_finiteWidth_horizontalEndpointHeight
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (widths : Finset Nat) (horizontalLeft horizontalRight : Nat -> Int)
    (y : Real) (minimumHeight : Nat)
    (hspan : forall width, width ∈ widths ->
      3 * B < horizontalRight width - horizontalLeft width)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists height : Nat, minimumHeight <= height /\
      forall width, width ∈ widths ->
        1 - epsilon < mu.real (E.horizontalCrossingEvent
          (horizontalLeft width) (horizontalRight width) y (y + height)) := by
  classical
  let Width := {width // width ∈ widths}
  have hexists (width : Width) : exists height : Nat,
      minimumHeight <= height /\
        1 - epsilon < mu.real (E.horizontalCrossingEvent
          (horizontalLeft width) (horizontalRight width) y (y + height)) := by
    let s : Real := 2 * horizontalLeft width - horizontalRight width
    let t : Int := 3 * (horizontalRight width - horizontalLeft width)
    have ht : 3 * B < t := by
      dsimp only [t]
      have hw := hspan width width.2
      push_cast
      nlinarith
    obtain ⟨height, hheight, hcrossing⟩ :=
      E.exists_horizontalCrossing_measureReal_gt_of_unique
        mu hFKG hTI hunique y B s hB0 hB t ht minimumHeight hepsilon
    refine ⟨height, hheight, ?_⟩
    convert hcrossing using 1 <;> dsimp only [s, t] <;> push_cast <;> ring
  let chosen : Width -> Nat := fun width => Classical.choose (hexists width)
  have hchosen (width : Width) := Classical.choose_spec (hexists width)
  let height := minimumHeight + ∑ width : Width, chosen width
  have hminimum : minimumHeight <= height := Nat.le_add_right _ _
  refine ⟨height, hminimum, ?_⟩
  intro width hwidth
  let indexed : Width := ⟨width, hwidth⟩
  have hchosen_le : chosen indexed <= height := by
    apply (Finset.single_le_sum
      (f := fun candidate : Width => chosen candidate)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ indexed)).trans
    exact Nat.le_add_left _ _
  have hmono := E.horizontalCrossingEvent_mono_vertical
    (a := (horizontalLeft width : Real))
    (b := (horizontalRight width : Real))
    (c' := y) (c := y) (d := y + chosen indexed) (d' := y + height)
    le_rfl (by gcongr)
  exact (hchosen indexed).2.trans_le (measureReal_mono hmono)



theorem PeriodicPlaneEmbedding.exists_finiteHeight_verticalEndpointWidth
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (heights : Finset Nat) (verticalBottom verticalTop : Nat -> Int)
    (x : Real) (minimumWidth : Nat)
    (hspan : forall height, height ∈ heights ->
      3 * B < verticalTop height - verticalBottom height)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists width : Nat, minimumWidth <= width /\
      forall height, height ∈ heights ->
        1 - epsilon < mu.real (E.verticalCrossingEvent
          x (x + width) (verticalBottom height) (verticalTop height)) := by
  classical
  let Height := {height // height ∈ heights}
  have hexists (height : Height) : exists width : Nat,
      minimumWidth <= width /\
        1 - epsilon < mu.real (E.verticalCrossingEvent
          x (x + width) (verticalBottom height) (verticalTop height)) := by
    let s : Real := 2 * verticalBottom height - verticalTop height
    let t : Int := 3 * (verticalTop height - verticalBottom height)
    have ht : 3 * B < t := by
      dsimp only [t]
      have hh := hspan height height.2
      push_cast
      nlinarith
    obtain ⟨width, hwidth, hcrossing⟩ :=
      E.exists_verticalCrossing_measureReal_gt_of_unique
        mu hFKG hTI hunique x B s hB0 hB t ht minimumWidth hepsilon
    refine ⟨width, hwidth, ?_⟩
    convert hcrossing using 1 <;> dsimp only [s, t] <;> push_cast <;> ring
  let chosen : Height -> Nat := fun height => Classical.choose (hexists height)
  have hchosen (height : Height) := Classical.choose_spec (hexists height)
  let width := minimumWidth + ∑ height : Height, chosen height
  have hminimum : minimumWidth <= width := Nat.le_add_right _ _
  refine ⟨width, hminimum, ?_⟩
  intro height hheight
  let indexed : Height := ⟨height, hheight⟩
  have hchosen_le : chosen indexed <= width := by
    apply (Finset.single_le_sum
      (f := fun candidate : Height => chosen candidate)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ indexed)).trans
    exact Nat.le_add_left _ _
  have hmono := E.verticalCrossingEvent_mono_horizontal
    (a' := x) (a := x) (b := x + chosen indexed) (b' := x + width)
    (c := (verticalBottom height : Real))
    (d := (verticalTop height : Real)) le_rfl (by gcongr)
  exact (hchosen indexed).2.trans_le (measureReal_mono hmono)





theorem PeriodicPlaneEmbedding.exists_finiteHeight_coupledEndpointWidthHeight
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (heights : Finset Nat) (verticalBottom verticalTop : Nat -> Int)
    (x y : Real) (minimumWidth minimumHeight : Nat)
    (horizontalLeft horizontalRight : Nat -> Int)
    (hverticalSpan : forall step, step ∈ heights ->
      3 * B < verticalTop step - verticalBottom step)
    (hhorizontalSpan : forall width, minimumWidth <= width ->
      3 * B < horizontalRight width - horizontalLeft width)
    {verticalEpsilon horizontalEpsilon : Real}
    (hVerticalEpsilon : 0 < verticalEpsilon)
    (hHorizontalEpsilon : 0 < horizontalEpsilon) :
    exists width height : Nat,
      minimumWidth <= width /\ minimumHeight <= height /\
      (forall step, step ∈ heights ->
        1 - verticalEpsilon < mu.real (E.verticalCrossingEvent
          x (x + width) (verticalBottom step) (verticalTop step))) /\
      1 - horizontalEpsilon < mu.real (E.horizontalCrossingEvent
        (horizontalLeft width) (horizontalRight width) y (y + height)) := by
  obtain ⟨width, hwidth, hvertical⟩ :=
    E.exists_finiteHeight_verticalEndpointWidth mu hFKG hTI hunique
      B hB0 hB heights verticalBottom verticalTop x minimumWidth
      hverticalSpan hVerticalEpsilon
  obtain ⟨height, hheight, hhorizontal⟩ :=
    E.exists_finiteWidth_horizontalEndpointHeight mu hFKG hTI hunique
      B hB0 hB {width} horizontalLeft horizontalRight y minimumHeight
      (fun candidate hcandidate => by
        simp only [Finset.mem_singleton] at hcandidate
        subst candidate
        exact hhorizontalSpan width hwidth)
      hHorizontalEpsilon
  refine ⟨width, height, hwidth, hheight, hvertical, ?_⟩
  exact hhorizontal width (Finset.mem_singleton_self width)




theorem PeriodicPlaneEmbedding.exists_finiteWidth_endpointHeight_pairMergeRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (template : Finset V) (widths : Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int)
    (y : Real) (minimumHeight cutoff : Nat)
    (hspan : forall width, width ∈ widths ->
      3 * B < horizontalRight width - horizontalLeft width)
    {endpointEpsilon mergeEpsilon : Real}
    (hEndpointEpsilon : 0 < endpointEpsilon)
    (hMergeEpsilon : 0 < mergeEpsilon) :
    exists height radius : Nat,
      minimumHeight <= height /\ cutoff <= radius /\
      (forall width, width ∈ widths ->
        1 - endpointEpsilon < mu.real (E.horizontalCrossingEvent
          (horizontalLeft width) (horizontalRight width) y (y + height))) /\
      forall step : Nat, step <= height ->
        forall q : Fin 2 × (Fin 3 × Fin 3),
          mu.real (P.pairMergeErrorUnion template
            (template.image (P.shift (preferenceKingOffset q.2 +
              if q.1.val = 0 then 0 else verticalShift step))) radius) <
            mergeEpsilon := by
  classical
  obtain ⟨height, hheight, hcrossing⟩ :=
    E.exists_finiteWidth_horizontalEndpointHeight mu hFKG hTI hunique
      B hB0 hB widths horizontalLeft horizontalRight y minimumHeight hspan
      hEndpointEpsilon
  let steps : Finset Int :=
    (Finset.range (height + 1)).image (fun step : Nat => (step : Int))
  obtain ⟨radius, hradius, hmerge⟩ :=
    P.exists_finiteAdjacentHeights_pairMergeRadius_at_error
      mu hunique template steps cutoff hMergeEpsilon
  refine ⟨height, radius, hheight, hradius, hcrossing, ?_⟩
  intro step hstep q
  apply hmerge (step : Int)
  simp only [steps, Finset.mem_image, Finset.mem_range]
  exact ⟨step, Nat.lt_succ_iff.mpr hstep, rfl⟩


structure PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (template : Finset V) (widths : Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int)
    (y : Real) (minimumHeight cutoff : Nat)
    (endpointEpsilon mergeEpsilon : Real) where
  height : Nat
  radius : Nat
  minimumHeight_le : minimumHeight <= height
  cutoff_le_radius : cutoff <= radius
  horizontalEndpoint : forall width, width ∈ widths ->
    1 - endpointEpsilon < mu.real (E.horizontalCrossingEvent
      (horizontalLeft width) (horizontalRight width) y (y + height))
  merge : forall step : Nat, step <= height ->
    forall q : Fin 2 × (Fin 3 × Fin 3),
      mu.real (P.pairMergeErrorUnion template
        (template.image (P.shift (preferenceKingOffset q.2 +
          if q.1.val = 0 then 0 else verticalShift step))) radius) <
        mergeEpsilon




structure PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.VerticalEndpointExtension
    {E : PeriodicPlaneEmbedding P}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {template : Finset V} {widths : Finset Nat}
    {horizontalLeft horizontalRight : Nat -> Int}
    {y : Real} {minimumHeight cutoff : Nat}
    {endpointEpsilon mergeEpsilon : Real}
    (row : E.FiniteWidthEndpointMergeRow mu template widths
      horizontalLeft horizontalRight y minimumHeight cutoff
      endpointEpsilon mergeEpsilon)
    (verticalBottom verticalTop : Nat -> Int)
    (x : Real) (minimumWidth : Nat) (verticalEndpointEpsilon : Real) where
  width : Nat
  minimumWidth_le : minimumWidth <= width
  verticalEndpoint : forall step : Nat, step <= row.height ->
    1 - verticalEndpointEpsilon < mu.real (E.verticalCrossingEvent
      x (x + width) (verticalBottom step) (verticalTop step))


theorem PeriodicPlaneEmbedding.nonempty_finiteWidthEndpointMergeRow
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (template : Finset V) (widths : Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int)
    (y : Real) (minimumHeight cutoff : Nat)
    (hspan : forall width, width ∈ widths ->
      3 * B < horizontalRight width - horizontalLeft width)
    {endpointEpsilon mergeEpsilon : Real}
    (hEndpointEpsilon : 0 < endpointEpsilon)
    (hMergeEpsilon : 0 < mergeEpsilon) :
    Nonempty (E.FiniteWidthEndpointMergeRow mu template widths
      horizontalLeft horizontalRight y minimumHeight cutoff
      endpointEpsilon mergeEpsilon) := by
  obtain ⟨height, radius, hheight, hradius, hhorizontal, hmerge⟩ :=
    E.exists_finiteWidth_endpointHeight_pairMergeRadius
      mu hFKG hTI hunique B hB0 hB template widths
      horizontalLeft horizontalRight y minimumHeight cutoff hspan
      hEndpointEpsilon hMergeEpsilon
  exact ⟨{
    height := height
    radius := radius
    minimumHeight_le := hheight
    cutoff_le_radius := hradius
    horizontalEndpoint := hhorizontal
    merge := hmerge }⟩



theorem PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.nonempty_verticalEndpointExtension
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (template : Finset V) (widths : Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int)
    (y : Real) (minimumHeight cutoff : Nat)
    (endpointEpsilon mergeEpsilon : Real)
    (row : E.FiniteWidthEndpointMergeRow mu template widths
      horizontalLeft horizontalRight y minimumHeight cutoff
      endpointEpsilon mergeEpsilon)
    (verticalBottom verticalTop : Nat -> Int)
    (x : Real) (minimumWidth : Nat) (verticalEndpointEpsilon : Real)
    (hspan : forall step : Nat, step <= row.height ->
      3 * B < verticalTop step - verticalBottom step)
    (hVerticalEndpointEpsilon : 0 < verticalEndpointEpsilon) :
    Nonempty (row.VerticalEndpointExtension verticalBottom verticalTop
      x minimumWidth verticalEndpointEpsilon) := by
  let heights : Finset Nat := Finset.range (row.height + 1)
  obtain ⟨width, hwidth, hvertical⟩ :=
    E.exists_finiteHeight_verticalEndpointWidth mu hFKG hTI hunique
      B hB0 hB heights verticalBottom verticalTop x minimumWidth
      (fun step hstep => hspan step (Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hstep))) hVerticalEndpointEpsilon
  exact ⟨{
    width := width
    minimumWidth_le := hwidth
    verticalEndpoint := fun step hstep =>
      hvertical step (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hstep)) }⟩




theorem PeriodicPlaneEmbedding.exists_recursiveFiniteWidthEndpointMergeRows
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (template : Nat -> Finset V) (initialWidths : Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int) (y : Real)
    (minimumHeight cutoff : Nat -> Nat)
    (endpointEpsilon mergeEpsilon : Nat -> Real)
    (hspan : forall width,
      3 * B < horizontalRight width - horizontalLeft width)
    (hEndpointEpsilon : forall n, 0 < endpointEpsilon n)
    (hMergeEpsilon : forall n, 0 < mergeEpsilon n) :
    exists widths : Nat -> Finset Nat,
      exists rows : forall n, E.FiniteWidthEndpointMergeRow mu
        (template n) (widths n) horizontalLeft horizontalRight y
        (minimumHeight n) (cutoff n) (endpointEpsilon n) (mergeEpsilon n),
        widths 0 = initialWidths /\
        (forall n, widths n ⊆ widths (n + 1)) /\
        forall n, E.connectorMarginRequirement (rows n).radius ∈
          widths (n + 1) := by
  classical
  let chooseRow (n : Nat) (widths : Finset Nat) :
      E.FiniteWidthEndpointMergeRow mu (template n) widths
        horizontalLeft horizontalRight y (minimumHeight n) (cutoff n)
        (endpointEpsilon n) (mergeEpsilon n) :=
    Classical.choice (E.nonempty_finiteWidthEndpointMergeRow
      mu hFKG hTI hunique B hB0 hB (template n) widths
      horizontalLeft horizontalRight y (minimumHeight n) (cutoff n)
      (fun width _ => hspan width) (hEndpointEpsilon n) (hMergeEpsilon n))
  let widths : Nat -> Finset Nat := fun n =>
    Nat.rec initialWidths (fun n current =>
      let row := chooseRow n current
      insert (E.connectorMarginRequirement row.radius) current) n
  let rows : forall n, E.FiniteWidthEndpointMergeRow mu
      (template n) (widths n) horizontalLeft horizontalRight y
      (minimumHeight n) (cutoff n) (endpointEpsilon n) (mergeEpsilon n) :=
    fun n => chooseRow n (widths n)
  refine ⟨widths, rows, rfl, ?_, ?_⟩
  · intro n
    simp only [widths]
    exact Finset.subset_insert _ _
  · intro n
    simp only [widths, rows]
    exact Finset.mem_insert_self
      (E.connectorMarginRequirement (chooseRow n (widths n)).radius)
      (widths n)




theorem PeriodicPlaneEmbedding.exists_recursiveMonotoneFiniteWidthEndpointMergeRows
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (template : Nat -> Finset V) (initialWidths : Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int) (y : Real)
    (minimumHeight cutoff : Nat -> Nat)
    (endpointEpsilon mergeEpsilon : Nat -> Real)
    (hspan : forall width,
      3 * B < horizontalRight width - horizontalLeft width)
    (hEndpointEpsilon : forall n, 0 < endpointEpsilon n)
    (hMergeEpsilon : forall n, 0 < mergeEpsilon n) :
    exists state : Nat -> Finset Nat × Nat,
      exists rows : forall n, E.FiniteWidthEndpointMergeRow mu
        (template n) (state n).1 horizontalLeft horizontalRight y
        (max (minimumHeight n) (state n).2) (cutoff n)
        (endpointEpsilon n) (mergeEpsilon n),
        state 0 = (initialWidths, 0) /\
        (forall n, state (n + 1) =
          (insert (E.connectorMarginRequirement (rows n).radius) (state n).1,
            (rows n).height)) /\
        (forall n, (state n).1 ⊆ (state (n + 1)).1) /\
        (forall n, E.connectorMarginRequirement (rows n).radius ∈
          (state (n + 1)).1) /\
        forall n, (rows n).height <= (rows (n + 1)).height := by
  classical
  let chooseRow (n : Nat) (state : Finset Nat × Nat) :
      E.FiniteWidthEndpointMergeRow mu (template n) state.1
        horizontalLeft horizontalRight y (max (minimumHeight n) state.2)
        (cutoff n) (endpointEpsilon n) (mergeEpsilon n) :=
    Classical.choice (E.nonempty_finiteWidthEndpointMergeRow
      mu hFKG hTI hunique B hB0 hB (template n) state.1
      horizontalLeft horizontalRight y (max (minimumHeight n) state.2)
      (cutoff n) (fun width _ => hspan width)
      (hEndpointEpsilon n) (hMergeEpsilon n))
  let state : Nat -> Finset Nat × Nat := fun n =>
    Nat.rec (initialWidths, 0) (fun n current =>
      let row := chooseRow n current
      (insert (E.connectorMarginRequirement row.radius) current.1,
        row.height)) n
  let rows : forall n, E.FiniteWidthEndpointMergeRow mu
      (template n) (state n).1 horizontalLeft horizontalRight y
      (max (minimumHeight n) (state n).2) (cutoff n)
      (endpointEpsilon n) (mergeEpsilon n) :=
    fun n => chooseRow n (state n)
  have hstateSucc (n : Nat) : state (n + 1) =
      (insert (E.connectorMarginRequirement (rows n).radius) (state n).1,
        (rows n).height) := by
    simp only [state, rows]
  refine ⟨state, rows, rfl, hstateSucc, ?_, ?_, ?_⟩
  · intro n
    rw [hstateSucc n]
    exact Finset.subset_insert _ _
  · intro n
    rw [hstateSucc n]
    exact Finset.mem_insert_self
      (E.connectorMarginRequirement (rows n).radius) (state n).1
  · intro n
    have hminimum := (rows (n + 1)).minimumHeight_le
    have hprevious : (state (n + 1)).2 = (rows n).height := by
      rw [hstateSucc n]
    exact hprevious.symm.le.trans
      ((Nat.le_max_right _ _).trans hminimum)



theorem PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.horizontalEndpoint_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (template : Nat -> Finset V) (widths : Nat -> Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int) (y : Real)
    (minimumHeight cutoff : Nat -> Nat)
    (endpointEpsilon mergeEpsilon : Nat -> Real)
    (rows : forall n, E.FiniteWidthEndpointMergeRow mu
      (template n) (widths n) horizontalLeft horizontalRight y
      (minimumHeight n) (cutoff n) (endpointEpsilon n) (mergeEpsilon n))
    (width : Nat -> Nat) (hwidth : forall n, width n ∈ widths n)
    (hepsilon : Tendsto endpointEpsilon atTop (nhds 0)) :
    Tendsto (fun n => mu.real (E.horizontalCrossingEvent
      (horizontalLeft (width n)) (horizontalRight (width n))
      y (y + (rows n).height))) atTop (nhds 1) := by
  have hlower : Tendsto (fun n => 1 - endpointEpsilon n)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilon
  exact hlower.squeeze tendsto_const_nhds
    (fun n => le_of_lt ((rows n).horizontalEndpoint (width n) (hwidth n)))
    (fun _ => measureReal_le_one)



theorem PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.VerticalEndpointExtension.verticalEndpoint_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (template : Nat -> Finset V) (widths : Nat -> Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int) (y : Real)
    (minimumHeight cutoff : Nat -> Nat)
    (endpointEpsilon mergeEpsilon : Nat -> Real)
    (rows : forall n, E.FiniteWidthEndpointMergeRow mu
      (template n) (widths n) horizontalLeft horizontalRight y
      (minimumHeight n) (cutoff n) (endpointEpsilon n) (mergeEpsilon n))
    (verticalBottom verticalTop : Nat -> Nat -> Int)
    (x : Nat -> Real) (minimumWidth : Nat -> Nat)
    (verticalEndpointEpsilon : Nat -> Real)
    (extensions : forall n, (rows n).VerticalEndpointExtension
      (verticalBottom n) (verticalTop n) (x n) (minimumWidth n)
      (verticalEndpointEpsilon n))
    (step : Nat -> Nat) (hstep : forall n, step n <= (rows n).height)
    (hepsilon : Tendsto verticalEndpointEpsilon atTop (nhds 0)) :
    Tendsto (fun n => mu.real (E.verticalCrossingEvent
      (x n) (x n + (extensions n).width)
      (verticalBottom n (step n)) (verticalTop n (step n))))
      atTop (nhds 1) := by
  have hlower : Tendsto (fun n => 1 - verticalEndpointEpsilon n)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilon
  exact hlower.squeeze tendsto_const_nhds
    (fun n => le_of_lt ((extensions n).verticalEndpoint (step n) (hstep n)))
    (fun _ => measureReal_le_one)



theorem PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.merge_tendsto_zero
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (template : Nat -> Finset V) (widths : Nat -> Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int) (y : Real)
    (minimumHeight cutoff : Nat -> Nat)
    (endpointEpsilon mergeEpsilon : Nat -> Real)
    (rows : forall n, E.FiniteWidthEndpointMergeRow mu
      (template n) (widths n) horizontalLeft horizontalRight y
      (minimumHeight n) (cutoff n) (endpointEpsilon n) (mergeEpsilon n))
    (step : Nat -> Nat) (hstep : forall n, step n <= (rows n).height)
    (q : Nat -> Fin 2 × (Fin 3 × Fin 3))
    (hepsilon : Tendsto mergeEpsilon atTop (nhds 0)) :
    Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
      ((template n).image (P.shift (preferenceKingOffset (q n).2 +
        if (q n).1.val = 0 then 0 else verticalShift (step n))))
      (rows n).radius)) atTop (nhds 0) := by
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => le_of_lt ((rows n).merge (step n) (hstep n) (q n))) hepsilon






theorem PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.centeredAdjacent_limit_of_pairMerge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (S : Nat -> Finset V) (margin M outerWidth outerHeight radius : Nat -> Nat)
    (score : Nat -> Real)
    (data : forall n, E.CommonSquareNormalBoundaryBandData
      mu (S n) (margin n) (M n) (score n))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n)
    (hMWidth : forall n, 2 * M n <= outerWidth n)
    (hMHeight : forall n, 2 * M n <= outerHeight n)
    (hwidth : forall n, 2 * margin n < outerWidth n - 2 * M n)
    (hheight : forall n, 2 * margin n < outerHeight n - 2 * M n)
    (hscore : Tendsto score atTop (nhds 1))
    (hscore_le : forall n, score n <= 1)
    (htemplateHit : Tendsto (fun n => mu.real
      (P.setHitsInfinite
        (P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight
          (data n).zBottom (data n).zTop : Set V))) atTop (nhds 1))
    (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion
        (P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight
          (data n).zBottom (data n).zTop)
        ((P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight
          (data n).zBottom (data n).zTop).image (P.shift
            (preferenceKingOffset (q n).2 +
              if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0))
    (hconnector : forall n
      (v : PreferenceGridVertex
        (outerWidth n - 2 * M n) (outerHeight n - 2 * M n)),
      margin n <= v.1.val ->
      v.1.val + margin n < outerWidth n - 2 * M n ->
      margin n <= v.2.val ->
      v.2.val + margin n < outerHeight n - 2 * M n ->
      (P.shift (preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (-(M n : Real))
            ((M n : Real) + (outerWidth n - 2 * M n : Nat))
            (-(M n : Real))
            ((M n : Real) + (outerHeight n - 2 * M n : Nat))) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        0 (outerWidth n) 0 (outerHeight n)))
      (mu.real (E.verticalCrossingEvent
        0 (outerWidth n) 0 (outerHeight n + step n))))
      atTop (nhds 1) := by
  have hcentered :=
    PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.primalAdjacent_limit_of_pairMerge
      E mu hFKG hTI S margin M (fun n => outerWidth n - 2 * M n)
      (fun n => outerHeight n - 2 * M n) radius score data step hstep
      hwidth hheight hscore hscore_le htemplateHit hmerge hconnector
  have hout := E.centeredCrossingMax_tendsto_origin mu hTI M outerWidth
    outerHeight (fun n => (step n).toNat) hMWidth hMHeight <| by
    apply hcentered.congr'
    filter_upwards [] with n
    have hstepCast : ((step n).toNat : Real) = step n := by
      exact_mod_cast Int.toNat_of_nonneg (hstep n)
    congr 3
    all_goals simp only [Nat.cast_add]
    rw [hstepCast]
  apply hout.congr'
  filter_upwards [] with n
  have hstepCast : ((step n).toNat : Real) = step n := by
    exact_mod_cast Int.toNat_of_nonneg (hstep n)
  congr 3
  rw [hstepCast]






theorem PeriodicPlanarDualPair.canonicalAdjacentHeightArray_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (width baseHeight K : Nat -> Nat)
    (hwidth : forall n, 10 * B < width n)
    (hheight : forall n, 10 * B < baseHeight n)
    (hverticalStart : Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (4 * B) (width n - 4 * B) 0 (baseHeight n)))
      atTop (nhds 1))
    (hhorizontalEnd : Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        0 (width n) (4 * B)
        ((baseHeight n + (K n + 1) : Nat) - 4 * B)))
      atTop (nhds 1))
    (hprimal : forall k : Nat -> Nat, (forall n, k n < K n + 1) ->
      Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          0 (width n) (4 * B)
          ((baseHeight n + k n : Nat) - 4 * B)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (4 * B) (width n - 4 * B) 0
          (baseHeight n + (k n + 1) : Nat)))) atTop (nhds 1))
    (hdual : forall k : Nat -> Nat, (forall n, k n <= K n + 1) ->
      Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (4 * B) (width n - 4 * B) 0
            (baseHeight n + k n : Nat)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            0 (width n) (4 * B)
            ((baseHeight n + k n : Nat) - 4 * B)))) atTop (nhds 1)) :
    False := by
  let a : Nat -> Nat -> Real := fun _ _ => 0
  let b : Nat -> Nat -> Real := fun n _ => width n
  let c : Nat -> Nat -> Real := fun _ _ => 0
  let d : Nat -> Nat -> Real := fun n k => baseHeight n + k
  apply D.adjacent_rectangles_contradiction_of_bounded_max_limits mu
    hBpos hBp hBd a b c d K
  · intro n k
    dsimp only [a, b]
    have hw := hwidth n
    push_cast at hw ⊢
    linarith
  · intro n k
    dsimp only [c, d]
    have hh := hheight n
    have hk : (0 : Real) <= k := by positivity
    push_cast at hh ⊢
    linarith
  · simpa only [a, b, c, d, Nat.cast_zero, Nat.cast_add,
      zero_add, add_zero] using hverticalStart
  · simpa only [a, b, c, d, Nat.cast_zero, Nat.cast_add,
      zero_add, add_assoc] using hhorizontalEnd
  · intro k hk
    simpa only [a, b, c, d, Nat.cast_zero, Nat.cast_add,
      zero_add, add_assoc] using hprimal k hk
  · intro k hk
    simpa only [a, b, c, d, Nat.cast_zero, Nat.cast_add,
      zero_add] using hdual k hk





theorem PeriodicPlaneEmbedding.exists_mixedAdjacentHeight_approxPreferredSide_crossing_branch
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Real)
    (step : Int) (hstep : 0 <= step)
    {width height : Nat} (hwidth : 0 < width) (hheight : 0 < height)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (source : PreferenceGridVertex width height -> Finset V)
    (bottom top left right : PreferenceGridVertex width height -> Real)
    (ha : a1 <= a0) (hb : b0 <= b1)
    (hc : c0 <= c1) (hd : d1 <= d0)
    (hsource : forall x, (source x : Set V) <=
      E.rectVertices a0 b0 c1 d1)
    (hbottomScore : forall x, bottom x = mu.real
      (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V)
        (E.rectBottomBoundaryVertices a1 b1 c1 d1)))
    (htopScore : forall x, top x = mu.real
      (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V)
        (E.rectTopBoundaryVertices a1 b1 c1 d1)))
    (hleftScore : forall x, left x = mu.real
      (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V)
        (E.rectLeftBoundaryVertices a0 b0 c0 d0)))
    (hrightScore : forall x, right x = mu.real
      (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V)
        (E.rectRightBoundaryVertices a0 b0 c0 d0)))
    (hbottom : forall i : Fin (width + 1),
      top (i, 0) <= bottom (i, 0) + epsilon)
    (htop : forall i : Fin (width + 1),
      bottom (i, Fin.last height) <= top (i, Fin.last height) + epsilon)
    (hleft : forall j : Fin (height + 1),
      right (0, j) <= left (0, j) + epsilon)
    (hright : forall j : Fin (height + 1),
      left (Fin.last width, j) <= right (Fin.last width, j) + epsilon) :
    exists x xVertical xHorizontal : PreferenceGridVertex width height,
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) /\
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) /\
      ((1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
          bottom x + epsilon /\
        let shifted := (source xVertical).image
          (P.shift (verticalShift step))
        let Mtransfer := mu.real
          (E.rectanglePairMergeErrorUnion a1 b1 c1 d1
            (source x) (source xVertical))
        let Mjoin := mu.real
          (E.rectanglePairMergeErrorUnion a1 b1 c1 (d1 + step)
            (source x) shifted)
        bottom x *
            (mu.real (P.setHitsInfinite (source xVertical : Set V)) *
              bottom x - Mtransfer - epsilon) - Mjoin <=
          mu.real (E.verticalCrossingEvent a1 b1 c1 (d1 + step))) \/
       (1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
          left x + epsilon /\
        let M := mu.real
          (E.rectanglePairMergeErrorUnion a0 b0 c0 d0
            (source x) (source xHorizontal))
        left x *
            (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) *
              left x - M - epsilon) - M <=
          mu.real (E.horizontalCrossingEvent a0 b0 c0 d0))) := by
  obtain ⟨x, xVertical, xHorizontal, hxBottom, hxLeft,
      hxVertical, hxVerticalOpposite, hxHorizontal,
      hxHorizontalOpposite⟩ :=
    exists_common_weak_approximate_preference_grid_witness
      hwidth hheight epsilon hepsilon bottom top left right
      hbottom htop hleft hright
  have hpref := E.preference_mixed_max_add_epsilon_ge_fourthRoot
    mu hFKG a0 b0 c0 d0 a1 b1 c1 d1 (source x : Set V)
      epsilon hepsilon ha hb hc hd (hsource x)
      (by simpa [hbottomScore x, htopScore x] using hxBottom)
      (by simpa [hleftScore x, hrightScore x] using hxLeft)
  have hpref' :
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        max (bottom x) (left x) + epsilon := by
    simpa [hbottomScore x, hleftScore x] using hpref
  refine ⟨x, xVertical, xHorizontal, hxVertical, hxHorizontal, ?_⟩
  by_cases hLB : left x <= bottom x
  · left
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        bottom x + epsilon := by
      simpa [max_eq_left hLB] using hpref'
    have htransfer :=
      E.adjacentHeightVerticalCrossing_ge_approxPreferredSide_transfer
        mu hFKG hTI a1 b1 c1 d1 step hstep
        (source x) (source xVertical) epsilon
        (by simpa [hbottomScore xVertical, htopScore xVertical] using
          hxVerticalOpposite)
    rw [<- hbottomScore x] at htransfer
    exact ⟨hroot, htransfer⟩
  · right
    have hBL : bottom x <= left x := le_of_not_ge hLB
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        left x + epsilon := by
      simpa [max_eq_right hBL] using hpref'
    have htransfer := E.horizontalCrossing_ge_approxPreferredSide_transfer
      mu hFKG a0 b0 c0 d0 (source x) (source xHorizontal) epsilon
      (by simpa [hleftScore xHorizontal, hrightScore xHorizontal] using
        hxHorizontalOpposite)
    rw [<- hleftScore x] at htransfer
    exact ⟨hroot, htransfer⟩

set_option linter.unusedVariables false in




theorem PeriodicPlaneEmbedding.mixedAdjacentHeightPreference_crossing_max_tendsto_one_of_pairMerge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (template : Nat -> Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n)
    (radius : Nat -> Nat)
    (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
        ((template n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0))
    (width height : Nat -> Nat)
    (hwidth : forall n, 0 < width n) (hheight : forall n, 0 < height n)
    (base : Nat -> Site 2)
    (a0 b0 c0 d0 a1 b1 c1 d1 epsilon : Nat -> Real)
    (bottom top left right : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Real)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilon0 : forall n, 0 <= epsilon n)
    (ha : forall n, a1 n <= a0 n) (hb : forall n, b0 n <= b1 n)
    (hc : forall n, c0 n <= c1 n) (hd : forall n, d1 n <= d0 n)
    (hsource : forall n (v : PreferenceGridVertex (width n) (height n)),
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V) <=
          E.rectVertices (a0 n) (b0 n) (c1 n) (d1 n))
    (hconnectorH : forall n
      (v : PreferenceGridVertex (width n) (height n)),
      (P.shift (base n + preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a0 n) (b0 n) (c0 n) (d0 n))
    (hconnectorV : forall n
      (v : PreferenceGridVertex (width n) (height n)),
      (P.shift (base n + preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a1 n) (b1 n) (c1 n) (d1 n))
    (hbottomScore : forall n v, bottom n v = mu.real
      (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectBottomBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n))))
    (htopScore : forall n v, top n v = mu.real
      (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectTopBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n))))
    (hleftScore : forall n v, left n v = mu.real
      (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectLeftBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n))))
    (hrightScore : forall n v, right n v = mu.real
      (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectRightBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n))))
    (hbottom : forall n i,
      top n (i, 0) <= bottom n (i, 0) + epsilon n)
    (htop : forall n i, bottom n (i, Fin.last (height n)) <=
      top n (i, Fin.last (height n)) + epsilon n)
    (hleft : forall n j,
      right n (0, j) <= left n (0, j) + epsilon n)
    (hright : forall n j, left n (Fin.last (width n), j) <=
      right n (Fin.last (width n), j) + epsilon n) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n) (d0 n)))
      (mu.real (E.verticalCrossingEvent
        (a1 n) (b1 n) (c1 n) (d1 n + step n)))) atTop (nhds 1) := by
  classical
  let neighbor : Nat -> (Fin 2 × (Fin 3 × Fin 3)) -> Finset V :=
    fun n q => (template n).image (P.shift
      (preferenceKingOffset q.2 +
        if q.1.val = 0 then 0 else verticalShift (step n)))
  have hwitness (n : Nat) :=
    E.exists_mixedAdjacentHeight_approxPreferredSide_crossing_branch
      mu hFKG hTI
      (a0 n) (b0 n) (c0 n) (d0 n)
      (a1 n) (b1 n) (c1 n) (d1 n) (step n) (hstep n)
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
  let source : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Finset V := fun n v =>
    (template n).image (P.shift (base n + preferenceGridSite v))
  let shiftedVerticalSource : Nat -> Finset V := fun n =>
    (source n (xVertical n)).image (P.shift (verticalShift (step n)))
  let z : Nat -> Site 2 := fun n => base n + preferenceGridSite (x n)
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
  have hneighbor0 (n : Nat) (ij : Fin 3 × Fin 3) :
      (neighbor n ((0 : Fin 2), ij)).image (P.shift (z n)) =
        (template n).image
          (P.shift (z n + preferenceKingOffset ij)) := by
    simp only [neighbor, Fin.isValue, Fin.val_zero, if_pos, add_zero,
      Finset.image_image]
    apply Finset.image_congr
    intro u hu
    simpa [add_comm] using
      (P.shift_add (preferenceKingOffset ij) (z n) u).symm
  have hneighbor1 (n : Nat) (ij : Fin 3 × Fin 3) :
      (neighbor n ((1 : Fin 2), ij)).image (P.shift (z n)) =
        ((template n).image
          (P.shift (z n + preferenceKingOffset ij))).image
            (P.shift (verticalShift (step n))) := by
    simp only [neighbor, Fin.isValue, Fin.val_one, one_ne_zero, if_false,
      Finset.image_image]
    apply Finset.image_congr
    intro u hu
    change P.shift (z n)
        (P.shift (preferenceKingOffset ij + verticalShift (step n)) u) =
      P.shift (verticalShift (step n))
        (P.shift (z n + preferenceKingOffset ij) u)
    rw [<- P.shift_add, <- P.shift_add]
    congr 2
    abel
  have hrectH (n : Nat) :
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a0 n) (b0 n) (c0 n) (d0 n) :=
    hconnectorH n (x n)
  have hrectV (n : Nat) :
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a1 n) (b1 n) (c1 n) (d1 n) :=
    hconnectorV n (x n)
  have hrectVTall (n : Nat) :
      (P.shift (z n) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a1 n) (b1 n) (c1 n) (d1 n + step n) := by
    have hs : (0 : Real) <= step n := by exact_mod_cast hstep n
    exact (hrectV n).trans
      (E.rectVertices_mono le_rfl le_rfl le_rfl (by linarith))
  have hMv00 :=
    E.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge
      mu hTI template (fun n => neighbor n ((0 : Fin 2), ijV n))
      radius z a1 b1 c1 d1 hrectV (by
        simpa only [neighbor] using
          hmerge (fun n => ((0 : Fin 2), ijV n)))
  have hMv10 :=
    E.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge
      mu hTI template (fun n => neighbor n ((1 : Fin 2), ijV n))
      radius z a1 b1 c1 (fun n => d1 n + step n) hrectVTall (by
        simpa only [neighbor] using
          hmerge (fun n => ((1 : Fin 2), ijV n)))
  have hMh0 :=
    E.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge
      mu hTI template (fun n => neighbor n ((0 : Fin 2), ijH n))
      radius z a0 b0 c0 d0 hrectH (by
        simpa only [neighbor] using
          hmerge (fun n => ((0 : Fin 2), ijH n)))
  let Mv0 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a1 n) (b1 n) (c1 n) (d1 n)
      (source n (x n)) (source n (xVertical n)))
  let Mv1 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a1 n) (b1 n) (c1 n)
      (d1 n + step n) (source n (x n)) (shiftedVerticalSource n))
  let Mv : Nat -> Real := fun n => Mv0 n + Mv1 n
  let Mh : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a0 n) (b0 n) (c0 n) (d0 n)
      (source n (x n)) (source n (xHorizontal n)))
  have hMv0 : Tendsto Mv0 atTop (nhds 0) := by
    simpa only [Mv0, source, z, hneighbor0, hzV] using hMv00
  have hMv1 : Tendsto Mv1 atTop (nhds 0) := by
    simpa only [Mv1, source, shiftedVerticalSource, z, hneighbor1, hzV]
      using hMv10
  have hMv : Tendsto Mv atTop (nhds 0) := by
    simpa only [Mv, zero_add] using hMv0.add hMv1
  have hMh : Tendsto Mh atTop (nhds 0) := by
    simpa only [Mh, source, z, hneighbor0, hzH] using hMh0
  let verticalBranch : Nat -> Prop := fun n =>
    1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))) <=
          bottom n (x n) + epsilon n /\
      bottom n (x n) *
          (mu.real (P.setHitsInfinite
              (source n (xVertical n) : Set V)) * bottom n (x n) -
            Mv0 n - epsilon n) - Mv1 n <=
        mu.real (E.verticalCrossingEvent
          (a1 n) (b1 n) (c1 n) (d1 n + step n))
  let A : Nat -> Real := fun n =>
    if verticalBranch n then bottom n (x n) else left n (x n)
  let Hv : Nat -> Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xVertical n) : Set V))
  let Hh : Nat -> Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xHorizontal n) : Set V))
  let Cv : Nat -> Real := fun n => mu.real
    (E.verticalCrossingEvent (a1 n) (b1 n) (c1 n) (d1 n + step n))
  let Ch : Nat -> Real := fun n => mu.real
    (E.horizontalCrossingEvent (a0 n) (b0 n) (c0 n) (d0 n))
  let root : Nat -> Real := fun n =>
    1 - Real.sqrt (Real.sqrt
      (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V))))
  have htranslatedHit (y : (n : Nat) ->
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
  have hrootA (n : Nat) : root n <= A n + epsilon n := by
    by_cases hv : verticalBranch n
    · simpa [A, root, hv] using hv.1
    · simpa [A, root, source, shiftedVerticalSource, Mv0, Mv1, Mh,
        hv] using ((hbranch n).resolve_left hv).1
  have hAupper (n : Nat) : A n <= 1 := by
    by_cases hv : verticalBranch n
    · simp only [A, if_pos hv]
      rw [hbottomScore n (x n)]
      exact measureReal_le_one
    · simp only [A, if_neg hv]
      rw [hleftScore n (x n)]
      exact measureReal_le_one
  have hcrossingBranch (n : Nat) :
      A n * (Hv n * A n - Mv n - epsilon n) - Mv n <= Cv n \/
      A n * (Hh n * A n - Mh n - epsilon n) - Mh n <= Ch n := by
    by_cases hv : verticalBranch n
    · left
      have hraw := hv.2
      have hA0 : 0 <= bottom n (x n) := by
        rw [hbottomScore]
        exact measureReal_nonneg
      have hM0 : 0 <= Mv0 n := measureReal_nonneg
      have hM1 : 0 <= Mv1 n := measureReal_nonneg
      simp only [A, if_pos hv, Hv, Cv, Mv] at ⊢
      nlinarith
    · right
      have hraw := ((hbranch n).resolve_left hv).2
      simpa [A, Hh, Ch, Mh, source, shiftedVerticalSource, Mv0, Mv1, hv]
        using hraw
  simpa [Cv, Ch, max_comm] using
    crossing_max_tendsto_one_of_approxPreferredSide_root_branches
      root A Hv Hh Mv Mh epsilon Cv Ch hroot hrootA hAupper
      hHv hHh hMv hMh hepsilon hcrossingBranch
      (fun _ => measureReal_le_one) (fun _ => measureReal_le_one)






theorem PeriodicPlaneEmbedding.exists_outward_mixed_approxPreferredSide_crossing_branch
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Real)
    (pad : Int) (hpad : 0 <= pad)
    {width height : Nat} (hwidth : 0 < width) (hheight : 0 < height)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (source : PreferenceGridVertex width height -> Finset V)
    (bottom top left right : PreferenceGridVertex width height -> Real)
    (ha : a1 <= a0) (hb : b0 <= b1)
    (hc : c0 <= c1) (hd : d1 <= d0)
    (hsource : forall x, (source x : Set V) <=
      E.rectVertices a0 b0 c1 d1)
    (hbottomScore : forall x, bottom x = mu.real
      (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V)
        (E.rectBottomBoundaryVertices a1 b1 c1 d1)))
    (htopScore : forall x, top x = mu.real
      (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V)
        (E.rectTopBoundaryVertices a1 b1 c1 d1)))
    (hleftScore : forall x, left x = mu.real
      (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V)
        (E.rectLeftBoundaryVertices a0 b0 c0 d0)))
    (hrightScore : forall x, right x = mu.real
      (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V)
        (E.rectRightBoundaryVertices a0 b0 c0 d0)))
    (hbottom : forall i : Fin (width + 1),
      top (i, 0) <= bottom (i, 0) + epsilon)
    (htop : forall i : Fin (width + 1),
      bottom (i, Fin.last height) <=
        top (i, Fin.last height) + epsilon)
    (hleft : forall j : Fin (height + 1),
      right (0, j) <= left (0, j) + epsilon)
    (hright : forall j : Fin (height + 1),
      left (Fin.last width, j) <=
        right (Fin.last width, j) + epsilon) :
    exists x xVertical xHorizontal : PreferenceGridVertex width height,
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) /\
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) /\
      ((1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
          bottom x + epsilon /\
        let Ldown := (source x).image
          (P.shift (verticalShift (-pad)))
        let Rdown := (source xVertical).image
          (P.shift (verticalShift (-pad)))
        let Rup := (source xVertical).image
          (P.shift (verticalShift pad))
        let Mtransfer := mu.real
          (E.rectanglePairMergeErrorUnion a1 b1
            (c1 - pad) (d1 - pad) Ldown Rdown)
        let Mjoin := mu.real
          (E.rectanglePairMergeErrorUnion a1 b1
            (c1 - pad) (d1 + pad) Ldown Rup)
        bottom x *
            (mu.real (P.setHitsInfinite (source xVertical : Set V)) *
              bottom x - Mtransfer - epsilon) - Mjoin <=
          mu.real (E.verticalCrossingEvent a1 b1
            (c1 - pad) (d1 + pad))) \/
       (1 - Real.sqrt (Real.sqrt
            (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
          left x + epsilon /\
        let Lleft := (source x).image
          (P.shift (horizontalShift (-pad)))
        let Rleft := (source xHorizontal).image
          (P.shift (horizontalShift (-pad)))
        let Rright := (source xHorizontal).image
          (P.shift (horizontalShift pad))
        let Mtransfer := mu.real
          (E.rectanglePairMergeErrorUnion
            (a0 - pad) (b0 - pad) c0 d0 Lleft Rleft)
        let Mjoin := mu.real
          (E.rectanglePairMergeErrorUnion
            (a0 - pad) (b0 + pad) c0 d0 Lleft Rright)
        left x *
            (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) *
              left x - Mtransfer - epsilon) - Mjoin <=
          mu.real (E.horizontalCrossingEvent
            (a0 - pad) (b0 + pad) c0 d0))) := by
  obtain ⟨x, xVertical, xHorizontal, hxBottom, hxLeft,
      hxVertical, hxVerticalOpposite, hxHorizontal,
      hxHorizontalOpposite⟩ :=
    exists_common_weak_approximate_preference_grid_witness
      hwidth hheight epsilon hepsilon bottom top left right
      hbottom htop hleft hright
  have hpref := E.preference_mixed_max_add_epsilon_ge_fourthRoot
    mu hFKG a0 b0 c0 d0 a1 b1 c1 d1 (source x : Set V)
      epsilon hepsilon ha hb hc hd (hsource x)
      (by simpa [hbottomScore x, htopScore x] using hxBottom)
      (by simpa [hleftScore x, hrightScore x] using hxLeft)
  have hpref' :
      1 - Real.sqrt (Real.sqrt
          (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        max (bottom x) (left x) + epsilon := by
    simpa [hbottomScore x, hleftScore x] using hpref
  refine ⟨x, xVertical, xHorizontal, hxVertical, hxHorizontal, ?_⟩
  by_cases hLB : left x <= bottom x
  · left
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        bottom x + epsilon := by
      simpa [max_eq_left hLB] using hpref'
    have htransfer :=
      E.outwardVerticalCrossing_ge_approxPreferredSide_transfer
        mu hFKG hTI a1 b1 c1 d1 pad hpad
        (source x) (source xVertical) epsilon
        (by simpa [hbottomScore xVertical, htopScore xVertical] using
          hxVerticalOpposite)
    rw [<- hbottomScore x] at htransfer
    exact ⟨hroot, htransfer⟩
  · right
    have hBL : bottom x <= left x := le_of_not_ge hLB
    have hroot : 1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <=
        left x + epsilon := by
      simpa [max_eq_right hBL] using hpref'
    have htransfer :=
      E.outwardHorizontalCrossing_ge_approxPreferredSide_transfer
        mu hFKG hTI a0 b0 c0 d0 pad hpad
        (source x) (source xHorizontal) epsilon
        (by simpa [hleftScore xHorizontal, hrightScore xHorizontal] using
          hxHorizontalOpposite)
    rw [<- hleftScore x] at htransfer
    exact ⟨hroot, htransfer⟩

set_option linter.unusedVariables false in



theorem PeriodicPlaneEmbedding.exists_uniformTemplate_outwardMixedPreference_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat -> Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n) :
    exists radius : Nat -> Nat, forall
      (width height : Nat -> Nat)
      (hwidth : forall n, 0 < width n)
      (hheight : forall n, 0 < height n)
      (base : Nat -> Site 2)
      (a0 b0 c0 d0 a1 b1 c1 d1 epsilon : Nat -> Real)
      (bottom top left right : (n : Nat) ->
        PreferenceGridVertex (width n) (height n) -> Real),
      Tendsto epsilon atTop (nhds 0) ->
      (forall n, 0 <= epsilon n) ->
      (forall n, a1 n <= a0 n) ->
      (forall n, b0 n <= b1 n) ->
      (forall n, c0 n <= c1 n) ->
      (forall n, d1 n <= d0 n) ->
      (forall n (v : PreferenceGridVertex (width n) (height n)),
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V) <=
            E.rectVertices (a0 n) (b0 n) (c1 n) (d1 n)) ->
      (forall n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            verticalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
            E.rectVertices (a1 n) (b1 n)
              (c1 n - pad n) (d1 n - pad n)) ->
      (forall n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            verticalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
            E.rectVertices (a1 n) (b1 n)
              (c1 n - pad n) (d1 n + pad n)) ->
      (forall n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            horizontalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
            E.rectVertices (a0 n - pad n) (b0 n - pad n)
              (c0 n) (d0 n)) ->
      (forall n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v +
            horizontalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
            E.rectVertices (a0 n - pad n) (b0 n + pad n)
              (c0 n) (d0 n)) ->
      (forall n v, bottom n v = mu.real
        (E.rectSideConnectionEvent
          (a1 n) (b1 n) (c1 n) (d1 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectBottomBoundaryVertices
            (a1 n) (b1 n) (c1 n) (d1 n)))) ->
      (forall n v, top n v = mu.real
        (E.rectSideConnectionEvent
          (a1 n) (b1 n) (c1 n) (d1 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectTopBoundaryVertices
            (a1 n) (b1 n) (c1 n) (d1 n)))) ->
      (forall n v, left n v = mu.real
        (E.rectSideConnectionEvent
          (a0 n) (b0 n) (c0 n) (d0 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectLeftBoundaryVertices
            (a0 n) (b0 n) (c0 n) (d0 n)))) ->
      (forall n v, right n v = mu.real
        (E.rectSideConnectionEvent
          (a0 n) (b0 n) (c0 n) (d0 n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectRightBoundaryVertices
            (a0 n) (b0 n) (c0 n) (d0 n)))) ->
      (forall n i, top n (i, 0) <= bottom n (i, 0) + epsilon n) ->
      (forall n i, bottom n (i, Fin.last (height n)) <=
        top n (i, Fin.last (height n)) + epsilon n) ->
      (forall n j, right n (0, j) <= left n (0, j) + epsilon n) ->
      (forall n j, left n (Fin.last (width n), j) <=
        right n (Fin.last (width n), j) + epsilon n) ->
      exists branch : Nat -> Bool,
        Tendsto (fun n => if branch n then
          mu.real (E.verticalCrossingEvent (a1 n) (b1 n)
            (c1 n - pad n) (d1 n + pad n))
        else
          mu.real (E.horizontalCrossingEvent
            (a0 n - pad n) (b0 n + pad n) (c0 n) (d0 n)))
          atTop (nhds 1) /\
        Tendsto (fun n => max
          (mu.real (E.verticalCrossingEvent (a1 n) (b1 n)
            (c1 n - pad n) (d1 n + pad n)))
          (mu.real (E.horizontalCrossingEvent
            (a0 n - pad n) (b0 n + pad n) (c0 n) (d0 n))))
          atTop (nhds 1) := by
  classical
  let neighbor : Nat -> (Fin 3 × (Fin 3 × Fin 3)) -> Finset V := fun n q =>
    (template n).image (P.shift (preferenceKingOffset q.2 +
      if q.1.val = 0 then 0 else if q.1.val = 1 then
        verticalShift (2 * pad n) else horizontalShift (2 * pad n)))
  obtain ⟨radius, _hradius, hmerge⟩ :=
    E.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      mu hTI hunique template neighbor
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight base
    a0 b0 c0 d0 a1 b1 c1 d1 epsilon bottom top left right
    hepsilon hepsilon0 ha hb hc hd hsource
    hconnectorV0 hconnectorV1 hconnectorH0 hconnectorH1
    hbottomScore htopScore hleftScore hrightScore
    hbottom htop hleft hright
  have hwitness (n : Nat) :=
    E.exists_outward_mixed_approxPreferredSide_crossing_branch
      mu hFKG hTI
      (a0 n) (b0 n) (c0 n) (d0 n)
      (a1 n) (b1 n) (c1 n) (d1 n) (pad n) (hpad n)
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
  let source : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Finset V := fun n v =>
    (template n).image (P.shift (base n + preferenceGridSite v))
  let zV : Nat -> Site 2 := fun n =>
    base n + preferenceGridSite (x n) + verticalShift (-(pad n))
  let zH : Nat -> Site 2 := fun n =>
    base n + preferenceGridSite (x n) + horizontalShift (-(pad n))
  have hneighbor (z : Nat -> Site 2) (n : Nat)
      (q : Fin 3 × (Fin 3 × Fin 3)) :
      (neighbor n q).image (P.shift (z n)) =
        (template n).image (P.shift (z n + preferenceKingOffset q.2 +
          if q.1.val = 0 then 0 else if q.1.val = 1 then
            verticalShift (2 * pad n) else horizontalShift (2 * pad n))) := by
    simp only [neighbor, Finset.image_image]
    apply Finset.image_congr
    intro u hu
    change P.shift (z n) (P.shift (preferenceKingOffset q.2 +
        (if q.1.val = 0 then 0 else if q.1.val = 1 then
          verticalShift (2 * pad n) else horizontalShift (2 * pad n))) u) =
      P.shift (z n + preferenceKingOffset q.2 +
        (if q.1.val = 0 then 0 else if q.1.val = 1 then
          verticalShift (2 * pad n) else horizontalShift (2 * pad n))) u
    rw [<- P.shift_add]
    congr 2
    abel
  have hzV (n : Nat) :
      zV n + preferenceKingOffset (ijV n) =
        base n + preferenceGridSite (xVertical n) +
          verticalShift (-(pad n)) := by
    dsimp only [zV]
    rw [hijV n]
    abel
  have hzH (n : Nat) :
      zH n + preferenceKingOffset (ijH n) =
        base n + preferenceGridSite (xHorizontal n) +
          horizontalShift (-(pad n)) := by
    dsimp only [zH]
    rw [hijH n]
    abel
  have hMv00 := hmerge zV (fun n => ((0 : Fin 3), ijV n))
    a1 b1 (fun n => c1 n - pad n) (fun n => d1 n - pad n)
    (fun n => hconnectorV0 n (x n))
  have hMv10 := hmerge zV (fun n => ((1 : Fin 3), ijV n))
    a1 b1 (fun n => c1 n - pad n) (fun n => d1 n + pad n)
    (fun n => hconnectorV1 n (x n))
  have hMh00 := hmerge zH (fun n => ((0 : Fin 3), ijH n))
    (fun n => a0 n - pad n) (fun n => b0 n - pad n) c0 d0
    (fun n => hconnectorH0 n (x n))
  have hMh10 := hmerge zH (fun n => ((2 : Fin 3), ijH n))
    (fun n => a0 n - pad n) (fun n => b0 n + pad n) c0 d0
    (fun n => hconnectorH1 n (x n))
  let Ldown : Nat -> Finset V := fun n =>
    (source n (x n)).image (P.shift (verticalShift (-(pad n))))
  let Rdown : Nat -> Finset V := fun n =>
    (source n (xVertical n)).image (P.shift (verticalShift (-(pad n))))
  let Rup : Nat -> Finset V := fun n =>
    (source n (xVertical n)).image (P.shift (verticalShift (pad n)))
  let Lleft : Nat -> Finset V := fun n =>
    (source n (x n)).image (P.shift (horizontalShift (-(pad n))))
  let Rleft : Nat -> Finset V := fun n =>
    (source n (xHorizontal n)).image (P.shift (horizontalShift (-(pad n))))
  let Rright : Nat -> Finset V := fun n =>
    (source n (xHorizontal n)).image (P.shift (horizontalShift (pad n)))
  have htranslatedSource (n : Nat)
      (v : PreferenceGridVertex (width n) (height n)) (s : Site 2) :
      (source n v).image (P.shift s) =
        (template n).image
          (P.shift (base n + preferenceGridSite v + s)) := by
    simp only [source, Finset.image_image]
    apply Finset.image_congr
    intro u hu
    change P.shift s (P.shift (base n + preferenceGridSite v) u) =
      P.shift (base n + preferenceGridSite v + s) u
    rw [<- P.shift_add]
  have hLdown (n : Nat) :
      (template n).image (P.shift (zV n)) = Ldown n := by
    exact (htranslatedSource n (x n) (verticalShift (-(pad n)))).symm
  have hRdown (n : Nat) :
      (neighbor n ((0 : Fin 3), ijV n)).image (P.shift (zV n)) =
        Rdown n := by
    rw [hneighbor]
    simp only [Fin.val_zero, if_pos, add_zero]
    rw [hzV]
    exact (htranslatedSource n (xVertical n)
      (verticalShift (-(pad n)))).symm
  have hRup (n : Nat) :
      (neighbor n ((1 : Fin 3), ijV n)).image (P.shift (zV n)) =
        Rup n := by
    rw [hneighbor]
    simp only [Fin.val_one, one_ne_zero, if_false, if_pos]
    have hs : zV n + preferenceKingOffset (ijV n) +
        verticalShift (2 * pad n) =
      base n + preferenceGridSite (xVertical n) + verticalShift (pad n) := by
      rw [hzV]
      ext i
      fin_cases i <;> simp [verticalShift] <;> omega
    rw [hs]
    exact (htranslatedSource n (xVertical n) (verticalShift (pad n))).symm
  have hLleft (n : Nat) :
      (template n).image (P.shift (zH n)) = Lleft n := by
    exact (htranslatedSource n (x n) (horizontalShift (-(pad n)))).symm
  have hRleft (n : Nat) :
      (neighbor n ((0 : Fin 3), ijH n)).image (P.shift (zH n)) =
        Rleft n := by
    rw [hneighbor]
    simp only [Fin.val_zero, if_pos, add_zero]
    rw [hzH]
    exact (htranslatedSource n (xHorizontal n)
      (horizontalShift (-(pad n)))).symm
  have hRright (n : Nat) :
      (neighbor n ((2 : Fin 3), ijH n)).image (P.shift (zH n)) =
        Rright n := by
    rw [hneighbor]
    change (template n).image (P.shift
      (zH n + preferenceKingOffset (ijH n) +
        horizontalShift (2 * pad n))) = Rright n
    have hs : zH n + preferenceKingOffset (ijH n) +
        horizontalShift (2 * pad n) =
      base n + preferenceGridSite (xHorizontal n) +
        horizontalShift (pad n) := by
      rw [hzH]
      ext i
      fin_cases i <;> simp [horizontalShift] <;> omega
    rw [hs]
    exact (htranslatedSource n (xHorizontal n)
      (horizontalShift (pad n))).symm
  let Mv0 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a1 n) (b1 n)
      (c1 n - pad n) (d1 n - pad n) (Ldown n) (Rdown n))
  let Mv1 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a1 n) (b1 n)
      (c1 n - pad n) (d1 n + pad n) (Ldown n) (Rup n))
  let Mh0 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a0 n - pad n) (b0 n - pad n)
      (c0 n) (d0 n) (Lleft n) (Rleft n))
  let Mh1 : Nat -> Real := fun n => mu.real
    (E.rectanglePairMergeErrorUnion (a0 n - pad n) (b0 n + pad n)
      (c0 n) (d0 n) (Lleft n) (Rright n))
  let Mv : Nat -> Real := fun n => Mv0 n + Mv1 n
  let Mh : Nat -> Real := fun n => Mh0 n + Mh1 n
  have hMv0 : Tendsto Mv0 atTop (nhds 0) := by
    simpa only [Mv0, hLdown, hRdown] using hMv00
  have hMv1 : Tendsto Mv1 atTop (nhds 0) := by
    simpa only [Mv1, hLdown, hRup] using hMv10
  have hMh0 : Tendsto Mh0 atTop (nhds 0) := by
    simpa only [Mh0, hLleft, hRleft] using hMh00
  have hMh1 : Tendsto Mh1 atTop (nhds 0) := by
    simpa only [Mh1, hLleft, hRright] using hMh10
  have hMv : Tendsto Mv atTop (nhds 0) := by
    simpa [Mv] using hMv0.add hMv1
  have hMh : Tendsto Mh atTop (nhds 0) := by
    simpa [Mh] using hMh0.add hMh1
  let verticalBranch : Nat -> Prop := fun n =>
    1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V)))) <=
          bottom n (x n) + epsilon n /\
      bottom n (x n) *
          (mu.real (P.setHitsInfinite
              (source n (xVertical n) : Set V)) * bottom n (x n) -
            Mv0 n - epsilon n) - Mv1 n <=
        mu.real (E.verticalCrossingEvent (a1 n) (b1 n)
          (c1 n - pad n) (d1 n + pad n))
  let A : Nat -> Real := fun n =>
    if verticalBranch n then bottom n (x n) else left n (x n)
  let Hv : Nat -> Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xVertical n) : Set V))
  let Hh : Nat -> Real := fun n =>
    mu.real (P.setHitsInfinite (source n (xHorizontal n) : Set V))
  let Cv : Nat -> Real := fun n => mu.real
    (E.verticalCrossingEvent (a1 n) (b1 n)
      (c1 n - pad n) (d1 n + pad n))
  let Ch : Nat -> Real := fun n => mu.real
    (E.horizontalCrossingEvent
      (a0 n - pad n) (b0 n + pad n) (c0 n) (d0 n))
  let root : Nat -> Real := fun n =>
    1 - Real.sqrt (Real.sqrt
      (1 - mu.real (P.setHitsInfinite (source n (x n) : Set V))))
  have htranslatedHit (y : (n : Nat) ->
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
  have hrootA (n : Nat) : root n <= A n + epsilon n := by
    by_cases hv : verticalBranch n
    · simpa [A, root, hv] using hv.1
    · simpa [A, root, source, Ldown, Rdown, Rup, Lleft, Rleft,
        Rright, Mv0, Mv1, Mh0, Mh1, hv] using
        ((hbranch n).resolve_left hv).1
  have hAupper (n : Nat) : A n <= 1 := by
    by_cases hv : verticalBranch n
    · simp only [A, if_pos hv]
      rw [hbottomScore n (x n)]
      exact measureReal_le_one
    · simp only [A, if_neg hv]
      rw [hleftScore n (x n)]
      exact measureReal_le_one
  have hcrossingBranch (n : Nat) :
      A n * (Hv n * A n - Mv n - epsilon n) - Mv n <= Cv n \/
      A n * (Hh n * A n - Mh n - epsilon n) - Mh n <= Ch n := by
    by_cases hv : verticalBranch n
    · left
      have hraw := hv.2
      have hA0 : 0 <= bottom n (x n) := by
        rw [hbottomScore]
        exact measureReal_nonneg
      have hM0 : 0 <= Mv0 n := measureReal_nonneg
      have hM1 : 0 <= Mv1 n := measureReal_nonneg
      simp only [A, if_pos hv, Hv, Cv, Mv] at ⊢
      nlinarith
    · right
      have hraw := ((hbranch n).resolve_left hv).2
      have hA0 : 0 <= left n (x n) := by
        rw [hleftScore]
        exact measureReal_nonneg
      have hM0 : 0 <= Mh0 n := measureReal_nonneg
      have hM1 : 0 <= Mh1 n := measureReal_nonneg
      have hraw' :
          left n (x n) *
              (Hh n * left n (x n) - Mh0 n - epsilon n) - Mh1 n <=
            Ch n := by
        simpa [Hh, Ch, source, Ldown, Rdown, Rup, Lleft, Rleft,
          Rright, Mv0, Mv1, Mh0, Mh1] using hraw
      simp only [A, if_neg hv, Hh, Ch, Mh]
      nlinarith [hraw']
  let selectedBranch : Nat -> Bool := fun n => decide (verticalBranch n)
  have hselectedVertical (n : Nat) (hselected : selectedBranch n = true) :
      A n * (Hv n * A n - Mv n - epsilon n) - Mv n <= Cv n := by
    have hv : verticalBranch n := of_decide_eq_true hselected
    have hraw := hv.2
    have hA0 : 0 <= bottom n (x n) := by
      rw [hbottomScore]
      exact measureReal_nonneg
    have hM0 : 0 <= Mv0 n := measureReal_nonneg
    have hM1 : 0 <= Mv1 n := measureReal_nonneg
    simp only [A, if_pos hv, Hv, Cv, Mv] at ⊢
    nlinarith
  have hselectedHorizontal (n : Nat)
      (hselected : selectedBranch n = false) :
      A n * (Hh n * A n - Mh n - epsilon n) - Mh n <= Ch n := by
    have hv : ¬ verticalBranch n := of_decide_eq_false hselected
    have hraw := ((hbranch n).resolve_left hv).2
    have hA0 : 0 <= left n (x n) := by
      rw [hleftScore]
      exact measureReal_nonneg
    have hM0 : 0 <= Mh0 n := measureReal_nonneg
    have hM1 : 0 <= Mh1 n := measureReal_nonneg
    have hraw' :
        left n (x n) *
            (Hh n * left n (x n) - Mh0 n - epsilon n) - Mh1 n <=
          Ch n := by
      simpa [Hh, Ch, source, Ldown, Rdown, Rup, Lleft, Rleft,
        Rright, Mv0, Mv1, Mh0, Mh1] using hraw
    simp only [A, if_neg hv, Hh, Ch, Mh]
    nlinarith [hraw']
  have hselected :=
    crossing_selected_tendsto_one_of_approxPreferredSide_root_branches
      selectedBranch root A Hv Hh Mv Mh epsilon Cv Ch
      hroot hrootA hAupper hHv hHh hMv hMh hepsilon
      hselectedVertical hselectedHorizontal
      (fun _ => measureReal_le_one) (fun _ => measureReal_le_one)
  have hmaximum :=
    crossing_max_tendsto_one_of_approxPreferredSide_root_branches
      root A Hv Hh Mv Mh epsilon Cv Ch hroot hrootA hAupper
      hHv hHh hMv hMh hepsilon hcrossingBranch
      (fun _ => measureReal_le_one) (fun _ => measureReal_le_one)
  refine ⟨selectedBranch, ?_, ?_⟩
  · simpa [Cv, Ch] using hselected
  · simpa [Cv, Ch] using hmaximum





theorem PeriodicPlaneEmbedding.exists_uniformOrbitBoxOutwardMixedRadius_alignedExact_dualLimit
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (p pDual : Nat -> Real)
    (family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n))
    (familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual
        (Pdual.orbitBox n) (pDual n))
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
    (schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n)
      (verticalRequirement n) (horizontalRequirement n))
    (hpDual : Tendsto pDual atTop (nhds 1))
    (hpDual_le : forall n, pDual n <= 1)
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n) :
    exists radius : Nat -> Nat,
      forall (k extentX extentY : Nat -> Nat)
        (data : forall n, AlignedExactExtentPairedMixedBoundaryScores
          E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
          (p n) (pDual n) (family n) (familyDual n) (schedule n)
          (k n) (extentX n) (extentY n)),
        (forall n, PairedAlignedConnectorSlack E Edual
          (family n) (familyDual n) (schedule n)
          (max (radius n) n) (k n)) ->
        Tendsto (fun n => max
          (muDual.real (Edual.verticalCrossingEvent
            (data n).raw.data.wideLeft (data n).raw.data.wideRight
            (0 - (pad n : Real)) ((extentY n : Real) + pad n)))
          (muDual.real (Edual.horizontalCrossingEvent
            (0 - (pad n : Real)) ((extentX n : Real) + pad n)
            0 (extentY n)))) atTop (nhds 1) := by
  let template : Nat -> Finset W := fun n => Pdual.orbitBox n
  have hexists :
      muDual {eta | Pdual.HasInfiniteCluster eta} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- huniqueDual]
    exact measure_mono fun _ h => h.1
  have htemplateHit : Tendsto (fun n =>
      muDual.real (Pdual.setHitsInfinite (template n : Set W)))
      atTop (nhds 1) := by
    simpa only [template, PeriodicGraph.setHitsInfinite,
      PeriodicGraph.orbitBoxHitsInfinite] using
      Pdual.orbitBoxHitsInfinite_real_tendsto_one muDual hexists
  obtain ⟨radius, hcross⟩ :=
    Edual.exists_uniformTemplate_outwardMixedPreference_crossing_max_tendsto_one
      muDual hFKGDual hTIDual huniqueDual template htemplateHit pad hpad
  refine ⟨radius, ?_⟩
  intro k extentX extentY data slack
  let epsilon : Nat -> Real := fun n => 1 - pDual n
  let bottom : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.widthDual)
        ((data n).raw.data.heightDual) -> Real := fun n v =>
    muDual.real (Edual.rectSideConnectionEvent
      (data n).raw.data.wideLeft (data n).raw.data.wideRight
      0 (extentY n)
      ((template n).image
        (Pdual.shift ((data n).raw.data.baseDual + preferenceGridSite v)) :
          Set W)
      (Edual.rectBottomBoundaryVertices
        (data n).raw.data.wideLeft (data n).raw.data.wideRight
        0 (extentY n)))
  let top : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.widthDual)
        ((data n).raw.data.heightDual) -> Real := fun n v =>
    muDual.real (Edual.rectSideConnectionEvent
      (data n).raw.data.wideLeft (data n).raw.data.wideRight
      0 (extentY n)
      ((template n).image
        (Pdual.shift ((data n).raw.data.baseDual + preferenceGridSite v)) :
          Set W)
      (Edual.rectTopBoundaryVertices
        (data n).raw.data.wideLeft (data n).raw.data.wideRight
        0 (extentY n)))
  let left : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.widthDual)
        ((data n).raw.data.heightDual) -> Real := fun n v =>
    muDual.real (Edual.rectSideConnectionEvent
      0 (extentX n) 0 (extentY n)
      ((template n).image
        (Pdual.shift ((data n).raw.data.baseDual + preferenceGridSite v)) :
          Set W)
      (Edual.rectLeftBoundaryVertices 0 (extentX n) 0 (extentY n)))
  let right : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.widthDual)
        ((data n).raw.data.heightDual) -> Real := fun n v =>
    muDual.real (Edual.rectSideConnectionEvent
      0 (extentX n) 0 (extentY n)
      ((template n).image
        (Pdual.shift ((data n).raw.data.baseDual + preferenceGridSite v)) :
          Set W)
      (Edual.rectRightBoundaryVertices 0 (extentX n) 0 (extentY n)))
  suffices hresult : exists branch : Nat -> Bool,
      Tendsto (fun n => if branch n then
        muDual.real (Edual.verticalCrossingEvent
          (data n).raw.data.wideLeft (data n).raw.data.wideRight
          (0 - (pad n : Real)) ((extentY n : Real) + pad n))
      else
        muDual.real (Edual.horizontalCrossingEvent
          (0 - (pad n : Real)) ((extentX n : Real) + pad n)
          0 (extentY n))) atTop (nhds 1) /\
      Tendsto (fun n => max
        (muDual.real (Edual.verticalCrossingEvent
          (data n).raw.data.wideLeft (data n).raw.data.wideRight
          (0 - (pad n : Real)) ((extentY n : Real) + pad n)))
        (muDual.real (Edual.horizontalCrossingEvent
          (0 - (pad n : Real)) ((extentX n : Real) + pad n)
          0 (extentY n)))) atTop (nhds 1) by
    obtain ⟨_branch, _hselected, hmaximum⟩ := hresult
    exact hmaximum
  apply hcross
      (fun n => (data n).raw.data.widthDual)
      (fun n => (data n).raw.data.heightDual)
      (fun n => (data n).raw.data.widthDual_pos)
      (fun n => (data n).raw.data.heightDual_pos)
      (fun n => (data n).raw.data.baseDual)
      (fun _ => 0) (fun n => (extentX n : Real))
      (fun _ => 0) (fun n => (extentY n : Real))
      (fun n => (data n).raw.data.wideLeft)
      (fun n => (data n).raw.data.wideRight)
      (fun _ => 0) (fun n => (extentY n : Real))
      epsilon bottom top left right
  · simpa [epsilon] using
      (tendsto_const_nhds (x := (1 : Real))).sub hpDual
  · exact fun n => sub_nonneg.mpr (hpDual_le n)
  · intro n
    exact (data n).raw.data.wideLeft_le
  · intro n
    simpa [(data n).raw.narrowRight_eq] using
      (data n).raw.data.narrowRight_le
  · intro n
    exact le_rfl
  · intro n
    exact le_rfl
  · intro n gridVertex vertex hvertex
    apply (data n).dualConnector_subset_narrow (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := by
      simpa only [template, Finset.mem_coe, Finset.mem_image] using hvertex
    refine ⟨sourceVertex, Pdual.orbitBox_mono ?_ hsourceVertex, rfl⟩
    exact (Nat.le_max_right (radius n) n).trans
      (Pdual.id_le_bufferedRadius (max (radius n) n))
  · intro n gridVertex vertex hvertex
    obtain ⟨u, hu, rfl⟩ := hvertex
    have hu' : u ∈ (Pdual.orbitBox
        (Pdual.bufferedRadius (max (radius n) n)) : Set W) :=
      Pdual.orbitBox_mono
        (Pdual.bufferedRadius_strictMono.monotone (Nat.le_max_left _ _)) hu
    have hcore0 := (data n).dualConnector_subset_wide
      (slack n) gridVertex ⟨u, hu', rfl⟩
    have hcore : Pdual.shift
        ((data n).raw.data.baseDual + preferenceGridSite gridVertex) u ∈
        Edual.rectVertices (data n).raw.data.wideLeft
          (data n).raw.data.wideRight 0 (extentY n) := by
      simpa [(data n).raw.shortTop_eq] using hcore0
    rw [show (data n).raw.data.baseDual + preferenceGridSite gridVertex +
        verticalShift (-(pad n)) =
      ((data n).raw.data.baseDual + preferenceGridSite gridVertex) +
        verticalShift (-(pad n)) by abel, Pdual.shift_add]
    have hshift := (Edual.shift_mem_rectVertices
      (verticalShift (-(pad n)))
      (data n).raw.data.wideLeft (data n).raw.data.wideRight
      0 (extentY n) _).2 hcore
    simpa [verticalShift] using hshift
  · intro n gridVertex vertex hvertex
    obtain ⟨u, hu, rfl⟩ := hvertex
    have hu' : u ∈ (Pdual.orbitBox
        (Pdual.bufferedRadius (max (radius n) n)) : Set W) :=
      Pdual.orbitBox_mono
        (Pdual.bufferedRadius_strictMono.monotone (Nat.le_max_left _ _)) hu
    have hcore0 := (data n).dualConnector_subset_wide
      (slack n) gridVertex ⟨u, hu', rfl⟩
    have hcore : Pdual.shift
        ((data n).raw.data.baseDual + preferenceGridSite gridVertex) u ∈
        Edual.rectVertices (data n).raw.data.wideLeft
          (data n).raw.data.wideRight 0 (extentY n) := by
      simpa [(data n).raw.shortTop_eq] using hcore0
    rw [show (data n).raw.data.baseDual + preferenceGridSite gridVertex +
        verticalShift (-(pad n)) =
      ((data n).raw.data.baseDual + preferenceGridSite gridVertex) +
        verticalShift (-(pad n)) by abel, Pdual.shift_add]
    have hshift := (Edual.shift_mem_rectVertices
      (verticalShift (-(pad n)))
      (data n).raw.data.wideLeft (data n).raw.data.wideRight
      0 (extentY n) _).2 hcore
    have hshift' : Pdual.shift (verticalShift (-(pad n)))
        (Pdual.shift
          ((data n).raw.data.baseDual + preferenceGridSite gridVertex) u) ∈
        Edual.rectVertices (data n).raw.data.wideLeft
          (data n).raw.data.wideRight (0 - (pad n : Real))
          ((extentY n : Real) - pad n) := by
      simpa [verticalShift] using hshift
    apply Edual.rectVertices_mono le_rfl le_rfl le_rfl _ hshift'
    have hp : (0 : Real) <= pad n := by exact_mod_cast hpad n
    push_cast
    linarith
  · intro n gridVertex vertex hvertex
    obtain ⟨u, hu, rfl⟩ := hvertex
    have hu' : u ∈ (Pdual.orbitBox
        (Pdual.bufferedRadius (max (radius n) n)) : Set W) :=
      Pdual.orbitBox_mono
        (Pdual.bufferedRadius_strictMono.monotone (Nat.le_max_left _ _)) hu
    have hcore0 := (data n).dualConnector_subset_narrow
      (slack n) gridVertex ⟨u, hu', rfl⟩
    have hcore : Pdual.shift
        ((data n).raw.data.baseDual + preferenceGridSite gridVertex) u ∈
        Edual.rectVertices 0 (extentX n) 0 (extentY n) := by
      simpa [(data n).raw.narrowRight_eq, (data n).raw.tallTop_eq]
        using hcore0
    rw [show (data n).raw.data.baseDual + preferenceGridSite gridVertex +
        horizontalShift (-(pad n)) =
      ((data n).raw.data.baseDual + preferenceGridSite gridVertex) +
        horizontalShift (-(pad n)) by abel, Pdual.shift_add]
    have hshift := (Edual.shift_mem_rectVertices
      (horizontalShift (-(pad n))) 0 (extentX n) 0 (extentY n) _).2 hcore
    simpa [horizontalShift] using hshift
  · intro n gridVertex vertex hvertex
    obtain ⟨u, hu, rfl⟩ := hvertex
    have hu' : u ∈ (Pdual.orbitBox
        (Pdual.bufferedRadius (max (radius n) n)) : Set W) :=
      Pdual.orbitBox_mono
        (Pdual.bufferedRadius_strictMono.monotone (Nat.le_max_left _ _)) hu
    have hcore0 := (data n).dualConnector_subset_narrow
      (slack n) gridVertex ⟨u, hu', rfl⟩
    have hcore : Pdual.shift
        ((data n).raw.data.baseDual + preferenceGridSite gridVertex) u ∈
        Edual.rectVertices 0 (extentX n) 0 (extentY n) := by
      simpa [(data n).raw.narrowRight_eq, (data n).raw.tallTop_eq]
        using hcore0
    rw [show (data n).raw.data.baseDual + preferenceGridSite gridVertex +
        horizontalShift (-(pad n)) =
      ((data n).raw.data.baseDual + preferenceGridSite gridVertex) +
        horizontalShift (-(pad n)) by abel, Pdual.shift_add]
    have hshift := (Edual.shift_mem_rectVertices
      (horizontalShift (-(pad n))) 0 (extentX n) 0 (extentY n) _).2 hcore
    have hshift' : Pdual.shift (horizontalShift (-(pad n)))
        (Pdual.shift
          ((data n).raw.data.baseDual + preferenceGridSite gridVertex) u) ∈
        Edual.rectVertices (0 - (pad n : Real))
          ((extentX n : Real) - pad n) 0 (extentY n) := by
      simpa [horizontalShift] using hshift
    apply Edual.rectVertices_mono le_rfl _ le_rfl le_rfl hshift'
    have hp : (0 : Real) <= pad n := by exact_mod_cast hpad n
    push_cast
    linarith
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n i
    have hTop : top n (i, 0) <= 1 := measureReal_le_one
    have hBottom : pDual n <= bottom n (i, 0) := by
      simpa [bottom, template, (data n).raw.shortTop_eq] using
        le_of_lt ((data n).raw.data.dual_bottom i)
    dsimp only [epsilon]
    linarith
  · intro n i
    have hBottom : bottom n (i, Fin.last ((data n).raw.data.heightDual)) <=
        1 := measureReal_le_one
    have hTop : pDual n <=
        top n (i, Fin.last ((data n).raw.data.heightDual)) := by
      simpa [top, template, (data n).raw.shortTop_eq] using
        le_of_lt ((data n).raw.data.dual_top i)
    dsimp only [epsilon]
    linarith
  · intro n j
    have hRight : right n (0, j) <= 1 := measureReal_le_one
    have hLeft : pDual n <= left n (0, j) := by
      simpa [left, template, (data n).raw.narrowRight_eq,
        (data n).raw.tallTop_eq] using
        le_of_lt ((data n).raw.data.dual_left j)
    dsimp only [epsilon]
    linarith
  · intro n j
    have hLeft : left n (Fin.last ((data n).raw.data.widthDual), j) <=
        1 := measureReal_le_one
    have hRight : pDual n <=
        right n (Fin.last ((data n).raw.data.widthDual), j) := by
      simpa [right, template, (data n).raw.narrowRight_eq,
        (data n).raw.tallTop_eq] using
        le_of_lt ((data n).raw.data.dual_right j)
    dsimp only [epsilon]
    linarith





theorem PeriodicPlaneEmbedding.alignedExact_primalMixedAdjacent_limit_of_pairMerge
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (p pDual : Nat -> Real)
    (family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n))
    (familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual
        (Pdual.orbitBox n) (pDual n))
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
    (schedule : forall n, PairedAlignedMarginSchedule E Edual
      (family n) (familyDual n)
      (verticalRequirement n) (horizontalRequirement n))
    (k extentX extentY step radius : Nat -> Nat)
    (data : forall n, AlignedExactExtentPairedMixedBoundaryScores
      E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
      (p n) (pDual n) (family n) (familyDual n) (schedule n)
      (k n) (extentX n) (extentY n))
    (slack : forall n, PairedAlignedConnectorSlack E Edual
      (family n) (familyDual n) (schedule n)
      (max (radius n) n) (k n))
    (hp : Tendsto p atTop (nhds 1)) (hp_le : forall n, p n <= 1)
    (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (P.orbitBox n)
        ((P.orbitBox n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        0 (extentX n) 0 (extentY n)))
      (mu.real (E.verticalCrossingEvent
        (data n).raw.data.wideLeft (data n).raw.data.wideRight
        0 (extentY n + step n)))) atTop (nhds 1) := by
  let template : Nat -> Finset V := fun n => P.orbitBox n
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [<- hunique]
    exact measure_mono fun _ h => h.1
  have htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
      atTop (nhds 1) := by
    simpa only [template, PeriodicGraph.setHitsInfinite,
      PeriodicGraph.orbitBoxHitsInfinite] using
      P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  let epsilon : Nat -> Real := fun n => 1 - p n
  let bottom : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.width)
        ((data n).raw.data.height) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent
      (data n).raw.data.wideLeft (data n).raw.data.wideRight
      0 (extentY n)
      ((template n).image
        (P.shift ((data n).raw.data.base + preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices
        (data n).raw.data.wideLeft (data n).raw.data.wideRight
        0 (extentY n)))
  let top : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.width)
        ((data n).raw.data.height) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent
      (data n).raw.data.wideLeft (data n).raw.data.wideRight
      0 (extentY n)
      ((template n).image
        (P.shift ((data n).raw.data.base + preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices
        (data n).raw.data.wideLeft (data n).raw.data.wideRight
        0 (extentY n)))
  let left : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.width)
        ((data n).raw.data.height) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent 0 (extentX n) 0 (extentY n)
      ((template n).image
        (P.shift ((data n).raw.data.base + preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices 0 (extentX n) 0 (extentY n)))
  let right : (n : Nat) ->
      PreferenceGridVertex ((data n).raw.data.width)
        ((data n).raw.data.height) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent 0 (extentX n) 0 (extentY n)
      ((template n).image
        (P.shift ((data n).raw.data.base + preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices 0 (extentX n) 0 (extentY n)))
  apply E.mixedAdjacentHeightPreference_crossing_max_tendsto_one_of_pairMerge
      mu hFKG hTI template htemplateHit (fun n => (step n : Int))
      (fun _ => Int.ofNat_zero_le _) radius
      (by simpa only [template] using hmerge)
      (fun n => (data n).raw.data.width)
      (fun n => (data n).raw.data.height)
      (fun n => (data n).raw.data.width_pos)
      (fun n => (data n).raw.data.height_pos)
      (fun n => (data n).raw.data.base)
      (fun _ => 0) (fun n => (extentX n : Real))
      (fun _ => 0) (fun n => (extentY n : Real))
      (fun n => (data n).raw.data.wideLeft)
      (fun n => (data n).raw.data.wideRight)
      (fun _ => 0) (fun n => (extentY n : Real))
      epsilon bottom top left right
  · simpa [epsilon] using
      (tendsto_const_nhds (x := (1 : Real))).sub hp
  · exact fun n => sub_nonneg.mpr (hp_le n)
  · exact fun n => (data n).raw.data.wideLeft_le
  · intro n
    simpa [(data n).raw.narrowRight_eq] using
      (data n).raw.data.narrowRight_le
  · exact fun _ => le_rfl
  · exact fun _ => le_rfl
  · intro n gridVertex vertex hvertex
    apply (data n).primalConnector_subset_narrow (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := by
      simpa only [template, Finset.mem_coe, Finset.mem_image] using hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    exact (Nat.le_max_right (radius n) n).trans
      (P.id_le_bufferedRadius (max (radius n) n))
  · intro n gridVertex vertex hvertex
    apply (data n).primalConnector_subset_narrow (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply P.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n gridVertex vertex hvertex
    rw [<- (data n).raw.shortTop_eq]
    apply (data n).primalConnector_subset_wide (slack n) gridVertex
    obtain ⟨sourceVertex, hsourceVertex, rfl⟩ := hvertex
    refine ⟨sourceVertex, P.orbitBox_mono ?_ hsourceVertex, rfl⟩
    apply P.bufferedRadius_strictMono.monotone
    exact Nat.le_max_left _ _
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n i
    have hTop : top n (i, 0) <= 1 := measureReal_le_one
    have hBottom : p n <= bottom n (i, 0) := by
      simpa [bottom, template, (data n).raw.shortTop_eq] using
        le_of_lt ((data n).raw.data.primal_bottom i)
    dsimp only [epsilon]
    linarith
  · intro n i
    have hBottom : bottom n (i, Fin.last ((data n).raw.data.height)) <=
        1 := measureReal_le_one
    have hTop : p n <= top n (i, Fin.last ((data n).raw.data.height)) := by
      simpa [top, template, (data n).raw.shortTop_eq] using
        le_of_lt ((data n).raw.data.primal_top i)
    dsimp only [epsilon]
    linarith
  · intro n j
    have hRight : right n (0, j) <= 1 := measureReal_le_one
    have hLeft : p n <= left n (0, j) := by
      simpa [left, template, (data n).raw.narrowRight_eq,
        (data n).raw.tallTop_eq] using
        le_of_lt ((data n).raw.data.primal_left j)
    dsimp only [epsilon]
    linarith
  · intro n j
    have hLeft : left n (Fin.last ((data n).raw.data.width), j) <=
        1 := measureReal_le_one
    have hRight : p n <=
        right n (Fin.last ((data n).raw.data.width), j) := by
      simpa [right, template, (data n).raw.narrowRight_eq,
        (data n).raw.tallTop_eq] using
        le_of_lt ((data n).raw.data.primal_right j)
    dsimp only [epsilon]
    linarith





theorem PairedAdjacentBoundaryBandScheduleData.alignedExact_primalAdjacent_limit
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {step : Nat -> Int}
    (scheduleData : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (k extentX extentY : Nat -> Nat)
    (exact : forall n, AlignedExactExtentPairedMixedBoundaryScores
      E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
      (scheduleData.score n) (scheduleData.scoreDual n)
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n) (k n) (extentX n) (extentY n))
    (slack : forall n, PairedAlignedConnectorSlack E Edual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n)
      (max (scheduleData.radius n) n) (k n)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        0 (extentX n) 0 (extentY n)))
      (mu.real (E.verticalCrossingEvent
        (exact n).raw.data.wideLeft (exact n).raw.data.wideRight
        0 (extentY n + (step n).toNat)))) atTop (nhds 1) := by
  apply E.alignedExact_primalMixedAdjacent_limit_of_pairMerge
    Edual mu muDual hFKG hTI hunique
    scheduleData.score scheduleData.scoreDual
    scheduleData.family scheduleData.familyDual
    (fun n _ => max
      (E.connectorMarginRequirement (scheduleData.radius n))
      (Edual.connectorMarginRequirement (scheduleData.radiusDual n)))
    (fun n _ => max
      (E.connectorMarginRequirement (scheduleData.radius n))
      (Edual.connectorMarginRequirement (scheduleData.radiusDual n)))
    scheduleData.schedule
    k extentX extentY (fun n => (step n).toNat) scheduleData.radius
    exact slack scheduleData.score_tendsto scheduleData.score_le_one
  intro q
  apply (scheduleData.primalMerge q).congr'
  filter_upwards [] with n
  have hstep : ((step n).toNat : Int) = step n :=
    Int.toNat_of_nonneg (scheduleData.step_nonneg n)
  simp only [hstep]




theorem PairedAdjacentBoundaryBandScheduleData.exists_alignedExact_dualOutwardRadius
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {step : Nat -> Int}
    (scheduleData : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n) :
    exists radius : Nat -> Nat,
      forall (k extentX extentY : Nat -> Nat)
        (exact : forall n, AlignedExactExtentPairedMixedBoundaryScores
          E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
          (scheduleData.score n) (scheduleData.scoreDual n)
          (scheduleData.family n) (scheduleData.familyDual n)
          (scheduleData.schedule n) (k n) (extentX n) (extentY n)),
        (forall n, PairedAlignedConnectorSlack E Edual
          (scheduleData.family n) (scheduleData.familyDual n)
          (scheduleData.schedule n) (max (radius n) n) (k n)) ->
        Tendsto (fun n => max
          (muDual.real (Edual.verticalCrossingEvent
            (exact n).raw.data.wideLeft (exact n).raw.data.wideRight
            (0 - (pad n : Real)) ((extentY n : Real) + pad n)))
          (muDual.real (Edual.horizontalCrossingEvent
            (0 - (pad n : Real)) ((extentX n : Real) + pad n)
            0 (extentY n)))) atTop (nhds 1) := by
  exact E.exists_uniformOrbitBoxOutwardMixedRadius_alignedExact_dualLimit
    Edual mu muDual hFKGDual hTIDual huniqueDual
    scheduleData.score scheduleData.scoreDual
    scheduleData.family scheduleData.familyDual
    (fun n _ => max
      (E.connectorMarginRequirement (scheduleData.radius n))
      (Edual.connectorMarginRequirement (scheduleData.radiusDual n)))
    (fun n _ => max
      (E.connectorMarginRequirement (scheduleData.radius n))
      (Edual.connectorMarginRequirement (scheduleData.radiusDual n)))
    scheduleData.schedule scheduleData.scoreDual_tendsto
    scheduleData.scoreDual_le_one pad hpad

omit [Countable V] in


theorem PeriodicPlaneEmbedding.orbitBoxCoordinateBound_mono_adaptive
    (E : PeriodicPlaneEmbedding P) {n m : Nat} (hnm : n <= m)
    (i : Fin 2) :
    E.orbitBoxCoordinateBound n i <= E.orbitBoxCoordinateBound m i := by
  classical
  unfold PeriodicPlaneEmbedding.orbitBoxCoordinateBound
  exact Finset.sup'_mono (fun v => |E.vertexCoord v i|)
    (fun _ hv => P.orbitBox_mono hnm hv)
    ⟨P.root, P.orbitBox_mono (Nat.zero_le n)
      P.root_mem_orbitBox_zero⟩

omit [Countable V] in


theorem PeriodicPlaneEmbedding.connectorMarginRequirement_mono_adaptive
    (E : PeriodicPlaneEmbedding P) {radius radius' : Nat}
    (h : radius <= radius') :
    E.connectorMarginRequirement radius <=
      E.connectorMarginRequirement radius' := by
  unfold PeriodicPlaneEmbedding.connectorMarginRequirement
  apply Nat.ceil_mono
  apply max_le_max
  · apply E.orbitBoxCoordinateBound_mono_adaptive
    exact P.bufferedRadius_strictMono.monotone h
  · apply E.orbitBoxCoordinateBound_mono_adaptive
    exact P.bufferedRadius_strictMono.monotone h

omit [Countable V] [Countable W] in


theorem PairedAlignedConnectorSlack.restrictRadius
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {radius radius' k : Nat} (h : radius <= radius')
    (slack : PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius' k) :
    PairedAlignedConnectorSlack E Edual family familyDual
      schedule radius k := by
  have hprimal := E.connectorMarginRequirement_mono_adaptive h
  have hdual := Edual.connectorMarginRequirement_mono_adaptive h
  have hprimalInt : (E.connectorMarginRequirement radius : Int) <=
      E.connectorMarginRequirement radius' := by
    exact_mod_cast hprimal
  have hdualInt : (Edual.connectorMarginRequirement radius : Int) <=
      Edual.connectorMarginRequirement radius' := by
    exact_mod_cast hdual
  exact {
    primalLeft := hprimalInt.trans slack.primalLeft
    primalRight := by
      have := slack.primalRight
      omega
    primalBottom := hprimalInt.trans slack.primalBottom
    primalTop := by
      have := slack.primalTop
      omega
    dualLeft := hdualInt.trans slack.dualLeft
    dualRight := by
      have := slack.dualRight
      omega
    dualBottom := hdualInt.trans slack.dualBottom
    dualTop := by
      have := slack.dualTop
      omega }




structure PairedAdjacentCrossNestedOutwardData
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    {step : Nat -> Int}
    (scheduleData : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step)
    (pad : Nat -> Int) (padding : Nat) where
  dualRadius : Nat -> Nat
  dualOutward :
    forall (k extentX extentY : Nat -> Nat)
      (exact : forall n, AlignedExactExtentPairedMixedBoundaryScores
        E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
        (scheduleData.score n) (scheduleData.scoreDual n)
        (scheduleData.family n) (scheduleData.familyDual n)
        (scheduleData.schedule n) (k n) (extentX n) (extentY n)),
      (forall n, PairedAlignedConnectorSlack E Edual
        (scheduleData.family n) (scheduleData.familyDual n)
        (scheduleData.schedule n) (max (dualRadius n) n) (k n)) ->
      Tendsto (fun n => max
        (muDual.real (Edual.verticalCrossingEvent
          (exact n).raw.data.wideLeft (exact n).raw.data.wideRight
          (0 - (pad n : Real)) ((extentY n : Real) + pad n)))
        (muDual.real (Edual.horizontalCrossingEvent
          (0 - (pad n : Real)) ((extentX n : Real) + pad n)
          0 (extentY n)))) atTop (nhds 1)
  index : Nat -> Nat
  slack : forall n, PairedAlignedConnectorSlack E Edual
    (scheduleData.family n) (scheduleData.familyDual n)
    (scheduleData.schedule n)
    (max (max (scheduleData.radius n) (dualRadius n)) n) (index n)
  triple : forall n, AlignedCrossNestedThreePairedMixedBoundaryScores
    E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
    (scheduleData.score n) (scheduleData.scoreDual n)
    (scheduleData.family n) (scheduleData.familyDual n)
    (scheduleData.schedule n) (index n) padding




theorem PairedAdjacentBoundaryBandScheduleData.exists_crossNestedOutwardData
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {step : Nat -> Int}
    (scheduleData : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step)
    (hTI : P.IsTranslationInvariant mu)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n)
    (padding : Nat) (lowerX lowerY : Nat -> Nat) :
    exists data : PairedAdjacentCrossNestedOutwardData
        E Edual mu muDual scheduleData pad padding,
      (forall n, lowerX n <= (data.triple n).currentX) /\
      (forall n, lowerY n <= (data.triple n).currentY) := by
  obtain ⟨dualRadius, hdual⟩ :=
    scheduleData.exists_alignedExact_dualOutwardRadius
      hFKGDual hTIDual huniqueDual pad hpad
  have hslack (n : Nat) := exists_pairedAlignedConnectorSlack E Edual
    (scheduleData.family n) (scheduleData.familyDual n)
    (scheduleData.schedule n)
    (max (max (scheduleData.radius n) (dualRadius n)) n)
  let index : Nat -> Nat := fun n => Classical.choose (hslack n)
  let slack : forall n, PairedAlignedConnectorSlack E Edual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n)
      (max (max (scheduleData.radius n) (dualRadius n)) n)
      (index n) := fun n => Classical.choose_spec (hslack n)
  have htriple (n : Nat) :=
    exists_alignedCrossNestedThreePairedMixedBoundaryScores_ge
      E Edual mu muDual hTI hTIDual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n) (index n) padding (lowerX n) (lowerY n)
  let triple : forall n, AlignedCrossNestedThreePairedMixedBoundaryScores
      E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
      (scheduleData.score n) (scheduleData.scoreDual n)
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n) (index n) padding := fun n =>
    Classical.choose (htriple n)
  let data : PairedAdjacentCrossNestedOutwardData
      E Edual mu muDual scheduleData pad padding := {
    dualRadius := dualRadius
    dualOutward := hdual
    index := index
    slack := slack
    triple := triple }
  refine ⟨data, ?_, ?_⟩
  · intro n
    exact (Classical.choose_spec (htriple n)).1
  · intro n
    exact (Classical.choose_spec (htriple n)).2.1




theorem PairedAdjacentCrossNestedOutwardData.local_limits
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {step : Nat -> Int}
    {scheduleData : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step}
    {pad : Nat -> Int} {padding : Nat}
    (data : PairedAdjacentCrossNestedOutwardData
      E Edual mu muDual scheduleData pad padding)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent 0
        (data.triple n).currentX 0 (data.triple n).currentY))
      (mu.real (E.verticalCrossingEvent
        (data.triple n).current.raw.data.wideLeft
        (data.triple n).current.raw.data.wideRight 0
        ((data.triple n).currentY + (step n).toNat))))
      atTop (nhds 1) /\
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight
        (0 - (pad n : Real))
        (((data.triple n).previousY : Real) + pad n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (0 - (pad n : Real))
        (((data.triple n).previousX : Real) + pad n)
        0 (data.triple n).previousY))) atTop (nhds 1) /\
    Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        (data.triple n).next.raw.data.wideLeft
        (data.triple n).next.raw.data.wideRight
        (0 - (pad n : Real))
        (((data.triple n).nextY : Real) + pad n)))
      (muDual.real (Edual.horizontalCrossingEvent
        (0 - (pad n : Real))
        (((data.triple n).nextX : Real) + pad n)
        0 (data.triple n).nextY))) atTop (nhds 1) := by
  have hprimalSlack : forall n, PairedAlignedConnectorSlack E Edual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n)
      (max (scheduleData.radius n) n) (data.index n) := by
    intro n
    apply (data.slack n).restrictRadius E Edual
    omega
  have hdualSlack : forall n, PairedAlignedConnectorSlack E Edual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n)
      (max (data.dualRadius n) n) (data.index n) := by
    intro n
    apply (data.slack n).restrictRadius E Edual
    omega
  refine ⟨scheduleData.alignedExact_primalAdjacent_limit hFKG hTI
      hunique data.index (fun n => (data.triple n).currentX)
      (fun n => (data.triple n).currentY)
      (fun n => (data.triple n).current) hprimalSlack, ?_, ?_⟩
  · exact data.dualOutward data.index
      (fun n => (data.triple n).previousX)
      (fun n => (data.triple n).previousY)
      (fun n => (data.triple n).previous) hdualSlack
  · exact data.dualOutward data.index
      (fun n => (data.triple n).nextX)
      (fun n => (data.triple n).nextY)
      (fun n => (data.triple n).next) hdualSlack





theorem PairedAdjacentCrossNestedOutwardData.shifted_matched_inequalities
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {step : Nat -> Int}
    {scheduleData : PairedAdjacentBoundaryBandScheduleData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) step}
    {pad : Nat -> Int} {padding : Nat}
    (data : PairedAdjacentCrossNestedOutwardData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      scheduleData pad padding)
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (hpadding : 4 * B <= (padding : Real))
    (hcurrentX : forall n, 10 * B < (data.triple n).currentX)
    (hcurrentY : forall n, 10 * B < (data.triple n).currentY) :
    (forall n,
      mu.real (D.primalEmbedding.horizontalCrossingEvent 0
          (data.triple n).currentX 0 (data.triple n).currentY) +
        (D.dualMeasure mu).real
          (D.dualEmbedding.verticalCrossingEvent
            (data.triple n).previous.raw.data.wideLeft
            (data.triple n).previous.raw.data.wideRight 0
            (data.triple n).previousY) <= 1) /\
    (forall n,
      mu.real (D.primalEmbedding.verticalCrossingEvent
          (data.triple n).current.raw.data.wideLeft
          (data.triple n).current.raw.data.wideRight 0
          (data.triple n).currentY) +
        (D.dualMeasure mu).real
          (D.dualEmbedding.horizontalCrossingEvent 0
            (data.triple n).nextX 0 (data.triple n).nextY) <= 1) := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  constructor
  · intro n
    let z : Site 2 := fun i => if i = 0 then
      padding - (data.triple n).previous.raw.wideLeftInt
      else -(padding : Int)
    have hcurrentXR : ((data.triple n).currentX : Real) =
        ((data.triple n).previous.raw.wideRightInt : Real) -
          (data.triple n).previous.raw.wideLeftInt + 2 * padding := by
      exact_mod_cast (data.triple n).currentX_eq
    have hpreviousYR : ((data.triple n).previousY : Real) =
        (data.triple n).currentY + 2 * padding := by
      exact_mod_cast (data.triple n).previousY_eq
    have hspanX : (0 : Real) + 5 * B <
        (data.triple n).currentX - 5 * B := by
      linarith [hcurrentX n]
    have hpad0 : (0 : Real) <= padding := by positivity
    have hspanY : -(padding : Real) + 5 * B <
        (data.triple n).currentY + padding - 5 * B := by
      linarith [hcurrentY n]
    have hbase := D.matchedCrossing_measureReal_add_le_one_of_pads
      mu hBpos hBp hBd hpadding hpadding hspanX hspanY
    have htranslated :=
      D.dualEmbedding.verticalCrossing_translate_measureReal_le
        (D.dualMeasure mu) hTIDual z
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
    have hdualLe :
        (D.dualMeasure mu).real
            (D.dualEmbedding.verticalCrossingEvent
              (data.triple n).previous.raw.data.wideLeft
              (data.triple n).previous.raw.data.wideRight 0
              (data.triple n).previousY) <=
          (D.dualMeasure mu).real
            (D.dualEmbedding.verticalCrossingEvent
              padding ((data.triple n).currentX - padding)
              (-padding) ((data.triple n).currentY + padding)) := by
      calc
        _ <= (D.dualMeasure mu).real
            (D.dualEmbedding.verticalCrossingEvent
              ((data.triple n).previous.raw.data.wideLeft + (z 0 : Real))
              ((data.triple n).previous.raw.data.wideRight + (z 0 : Real))
              (0 + (z 1 : Real))
              ((data.triple n).previousY + (z 1 : Real))) := htranslated
        _ = _ := by
          apply congrArg (fun event : Set (ConfigSpace (Sym2 W)) =>
            (D.dualMeasure mu).real event)
          congr 1
          all_goals
            simp only [z, Pi.zero_apply, if_pos, if_neg]
          · rw [(data.triple n).previous.raw.wideLeft_eq]
            push_cast
            ring
          · rw [(data.triple n).previous.raw.wideRight_eq]
            push_cast
            linarith [hcurrentXR]
          · push_cast
            ring
          · push_cast
            linarith [hpreviousYR]
    simp_rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)] at hdualLe
    have hbase' :
        mu.real (D.primalEmbedding.horizontalCrossingEvent 0
            (data.triple n).currentX 0 (data.triple n).currentY) +
          mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
            D.dualEmbedding.verticalCrossingEvent
              padding ((data.triple n).currentX - padding)
              (-padding) ((data.triple n).currentY + padding)) <= 1 := by
      simpa only [zero_add, neg_add_cancel, sub_neg_eq_add,
        add_sub_cancel_right, sub_add_cancel] using hbase
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
    linarith
  · intro n
    let z : Site 2 := fun i => if i = 0 then
      (data.triple n).current.raw.wideLeftInt - padding
      else (padding : Int)
    have hnextXR : ((data.triple n).nextX : Real) =
        ((data.triple n).current.raw.wideRightInt : Real) -
          (data.triple n).current.raw.wideLeftInt + 2 * padding := by
      exact_mod_cast (data.triple n).nextX_eq
    have hcurrentYR : ((data.triple n).currentY : Real) =
        (data.triple n).nextY + 2 * padding := by
      exact_mod_cast (data.triple n).currentY_eq
    have hwideSpan : ((data.triple n).currentX : Real) <=
        (data.triple n).current.raw.wideRightInt -
          (data.triple n).current.raw.wideLeftInt := by
      exact_mod_cast (data.triple n).current.raw.extentX_le_wideSpan
    have hspanX :
        (data.triple n).current.raw.data.wideLeft - padding + 5 * B <
          (data.triple n).current.raw.data.wideRight + padding - 5 * B := by
      rw [(data.triple n).current.raw.wideLeft_eq,
        (data.triple n).current.raw.wideRight_eq]
      push_cast
      have hpad0 : (0 : Real) <= padding := by positivity
      linarith [hcurrentX n]
    have hspanY : (0 : Real) + 5 * B <
        (data.triple n).currentY - 5 * B := by
      linarith [hcurrentY n]
    have hbase :=
      D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads
        mu hBpos hBp hBd hpadding hpadding hspanX hspanY
    have htranslated :=
      D.dualEmbedding.horizontalCrossing_translate_measureReal_le
        (D.dualMeasure mu) hTIDual z 0 (data.triple n).nextX 0
        (data.triple n).nextY
    have hdualLe :
        (D.dualMeasure mu).real
            (D.dualEmbedding.horizontalCrossingEvent 0
              (data.triple n).nextX 0 (data.triple n).nextY) <=
          (D.dualMeasure mu).real
            (D.dualEmbedding.horizontalCrossingEvent
              ((data.triple n).current.raw.data.wideLeft - padding)
              ((data.triple n).current.raw.data.wideRight + padding)
              padding ((data.triple n).currentY - padding)) := by
      calc
        _ <= (D.dualMeasure mu).real
            (D.dualEmbedding.horizontalCrossingEvent
              (0 + (z 0 : Real))
              ((data.triple n).nextX + (z 0 : Real))
              (0 + (z 1 : Real))
              ((data.triple n).nextY + (z 1 : Real))) := htranslated
        _ = _ := by
          apply congrArg (fun event : Set (ConfigSpace (Sym2 W)) =>
            (D.dualMeasure mu).real event)
          congr 1
          all_goals
            simp only [z, Pi.zero_apply, if_pos, if_neg]
          · rw [(data.triple n).current.raw.wideLeft_eq]
            push_cast
            ring
          · rw [(data.triple n).current.raw.wideRight_eq]
            push_cast
            linarith [hnextXR]
          · push_cast
            ring
          · push_cast
            linarith [hcurrentYR]
    simp_rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)] at hdualLe
    have hbase' :
        mu.real (D.primalEmbedding.verticalCrossingEvent
            (data.triple n).current.raw.data.wideLeft
            (data.triple n).current.raw.data.wideRight 0
            (data.triple n).currentY) +
          mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
            D.dualEmbedding.horizontalCrossingEvent
              ((data.triple n).current.raw.data.wideLeft - padding)
              ((data.triple n).current.raw.data.wideRight + padding)
              padding ((data.triple n).currentY - padding)) <= 1 := by
      simpa only [zero_add, add_sub_cancel_right, sub_add_cancel] using hbase
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
    linarith



theorem adjacent_height_array_contradiction_of_primal_dual_bounded_limits_of_bounded_matches
    (horizontal vertical dualVertical dualHorizontal : Nat -> Nat -> Real)
    (K : Nat -> Nat)
    (hhorizontal_nonneg : forall n k, 0 <= horizontal n k)
    (hvertical_nonneg : forall n k, 0 <= vertical n k)
    (hhorizontal_le_one : forall n k, horizontal n k <= 1)
    (hvertical_le_one : forall n k, vertical n k <= 1)
    (hvertical_start : Tendsto (fun n => vertical n 0) atTop (nhds 1))
    (hhorizontal_end : Tendsto (fun n => horizontal n (K n + 1))
      atTop (nhds 1))
    (hmatchHorizontal : forall n k, k <= K n + 1 ->
      horizontal n k + dualVertical n k <= 1)
    (hmatchVertical : forall n k, k <= K n + 1 ->
      vertical n k + dualHorizontal n k <= 1)
    (hprimalLimits : forall k : Nat -> Nat,
      (forall n, k n < K n + 1) -> Tendsto (fun n => max
        (horizontal n (k n)) (vertical n (k n + 1)))
        atTop (nhds 1))
    (hdualLimits : forall k : Nat -> Nat,
      (forall n, k n <= K n + 1) -> Tendsto (fun n => max
        (dualVertical n (k n)) (dualHorizontal n (k n)))
        atTop (nhds 1)) : False := by
  apply adjacent_height_array_contradiction_of_endpoint_and_uniform_limits
    horizontal vertical K hhorizontal_nonneg hvertical_nonneg
    hhorizontal_le_one hvertical_le_one hvertical_start hhorizontal_end
  intro k hk
  have hkBound : forall n, k n <= K n + 1 := fun n => (hk n).le
  have hkNextBound : forall n, k n + 1 <= K n + 1 := by
    intro n
    exact Nat.succ_le_of_lt (hk n)
  refine ⟨hprimalLimits k hk, ?_, ?_⟩
  · simpa only [min_comm] using min_tendsto_zero_of_matched_exclusion
      (fun n => horizontal n (k n))
      (fun n => vertical n (k n))
      (fun n => dualVertical n (k n))
      (fun n => dualHorizontal n (k n))
      (fun n => hhorizontal_nonneg n (k n))
      (fun n => hvertical_nonneg n (k n))
      (fun n => hmatchHorizontal n (k n) (hkBound n))
      (fun n => hmatchVertical n (k n) (hkBound n))
      (hdualLimits k hkBound)
  · simpa only [min_comm] using min_tendsto_zero_of_matched_exclusion
      (fun n => horizontal n (k n + 1))
      (fun n => vertical n (k n + 1))
      (fun n => dualVertical n (k n + 1))
      (fun n => dualHorizontal n (k n + 1))
      (fun n => hhorizontal_nonneg n (k n + 1))
      (fun n => hvertical_nonneg n (k n + 1))
      (fun n => hmatchHorizontal n (k n + 1) (hkNextBound n))
      (fun n => hmatchVertical n (k n + 1) (hkNextBound n))
      (hdualLimits (fun n => k n + 1) hkNextBound)




theorem shifted_crossNested_array_contradiction_of_bounded_limits
    (horizontal vertical dualVertical dualHorizontal : Nat -> Nat -> Real)
    (K : Nat -> Nat)
    (hhorizontal_nonneg : forall n k, 0 <= horizontal n k)
    (hvertical_nonneg : forall n k, 0 <= vertical n k)
    (hhorizontal_le_one : forall n k, horizontal n k <= 1)
    (hvertical_le_one : forall n k, vertical n k <= 1)
    (hvertical_start : Tendsto (fun n => vertical n 0)
      atTop (nhds 1))
    (hhorizontal_end : Tendsto (fun n =>
      horizontal n (2 * (K n + 1) + 2)) atTop (nhds 1))
    (hmatchHorizontal : forall n k, k < 2 * (K n + 1) + 2 ->
      horizontal n (k + 1) + dualVertical n k <= 1)
    (hmatchVertical : forall n k, k < 2 * (K n + 1) + 2 ->
      vertical n k + dualHorizontal n (k + 1) <= 1)
    (hprimalLimits : forall k : Nat -> Nat,
      (forall n, k n < K n + 1) -> Tendsto (fun n => max
        (horizontal n (2 * k n + 2))
        (vertical n (2 * k n + 2))) atTop (nhds 1))
    (hdualLimits : forall k : Nat -> Nat,
      (forall n, k n <= K n + 1) -> Tendsto (fun n => max
        (dualVertical n (2 * k n + 1))
        (dualHorizontal n (2 * k n + 1))) atTop (nhds 1)) : False := by
  let horizontal' : Nat -> Nat -> Real := fun n k =>
    horizontal n (2 * k + 2)
  let vertical' : Nat -> Nat -> Real := fun n k =>
    vertical n (2 * k)
  let dualVertical' : Nat -> Nat -> Real := fun n k =>
    dualVertical n (2 * k + 1)
  let dualHorizontal' : Nat -> Nat -> Real := fun n k =>
    dualHorizontal n (2 * k + 1)
  apply adjacent_height_array_contradiction_of_primal_dual_bounded_limits_of_bounded_matches
    horizontal' vertical' dualVertical' dualHorizontal' K
  · intro n k
    exact hhorizontal_nonneg n _
  · intro n k
    exact hvertical_nonneg n _
  · intro n k
    exact hhorizontal_le_one n _
  · intro n k
    exact hvertical_le_one n _
  · simpa only [vertical', mul_zero] using hvertical_start
  · simpa only [horizontal'] using hhorizontal_end
  · intro n k hk
    simpa only [horizontal', dualVertical'] using
      hmatchHorizontal n (2 * k + 1) (by omega)
  · intro n k hk
    simpa only [vertical', dualHorizontal'] using
      hmatchVertical n (2 * k) (by omega)
  · intro k hk
    simpa only [horizontal', vertical', Nat.mul_add,
      Nat.mul_one, Nat.add_assoc] using hprimalLimits k hk
  · intro k hk
    simpa only [dualVertical', dualHorizontal'] using hdualLimits k hk



structure AlignedCrossNestedPairedChain
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Finset V) (Sdual : Finset W) (p pDual : Real)
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding length : Nat) where
  extentX : Nat -> Nat
  extentY : Nat -> Nat
  level : forall j, AlignedExactExtentPairedMixedBoundaryScores
    E Edual mu muDual S Sdual p pDual family familyDual schedule k
      (extentX j) (extentY j)
  nextX_eq : forall j, j < length ->
    (extentX (j + 1) : Int) =
      (level j).raw.wideRightInt - (level j).raw.wideLeftInt +
        2 * padding
  nextY_eq : forall j, j < length ->
    extentY j = extentY (j + 1) + 2 * padding






theorem AlignedCrossNestedPairedChain.extentX_eq_of_zero_eq
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k padding length : Nat}
    (first second : AlignedCrossNestedPairedChain E Edual mu muDual
      S Sdual p pDual family familyDual schedule k padding length)
    (hzero : first.extentX 0 = second.extentX 0) :
    forall j, j <= length -> first.extentX j = second.extentX j := by
  intro j hj
  induction j with
  | zero => exact hzero
  | succ j ih =>
      have hjlt : j < length := by omega
      have hfirst := first.nextX_eq j hjlt
      have hsecond := second.nextX_eq j hjlt
      rw [(first.level j).wideSpan_formula, ih (by omega)] at hfirst
      rw [(second.level j).wideSpan_formula] at hsecond
      exact_mod_cast hfirst.trans hsecond.symm




theorem AlignedCrossNestedPairedChain.extentY_eq_terminal_add
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k padding length : Nat}
    (data : AlignedCrossNestedPairedChain E Edual mu muDual
      S Sdual p pDual family familyDual schedule k padding length)
    {j : Nat} (hj : j <= length) :
    data.extentY j = data.extentY length + 2 * padding * (length - j) := by
  have hgap : j + (length - j) = length := by omega
  generalize hd : length - j = d at hgap ⊢
  induction d generalizing j with
  | zero =>
      have hjlen : j = length := by omega
      subst j
      simp
  | succ d ih =>
      have hjlt : j < length := by omega
      calc
        data.extentY j = data.extentY (j + 1) + 2 * padding :=
          data.nextY_eq j hjlt
        _ = (data.extentY length + 2 * padding * d) + 2 * padding := by
          rw [ih (j := j + 1) (by omega) (by omega) (by omega)]
        _ = data.extentY length + 2 * padding * (d + 1) := by ring




theorem AlignedCrossNestedPairedChain.extentY_eq_of_terminal_eq
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement}
    {k padding length : Nat}
    (first second : AlignedCrossNestedPairedChain E Edual mu muDual
      S Sdual p pDual family familyDual schedule k padding length)
    (hterminal : first.extentY length = second.extentY length) :
    forall j, j <= length -> first.extentY j = second.extentY j := by
  intro j hj
  rw [first.extentY_eq_terminal_add hj,
    second.extentY_eq_terminal_add hj, hterminal]





theorem exists_alignedCrossNestedPairedChain_at_endpoints
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding length : Nat) :
    exists thresholdX thresholdY : Nat,
      forall (initialX terminalY : Nat),
        thresholdX <= initialX -> thresholdY <= terminalY ->
        exists data : AlignedCrossNestedPairedChain E Edual mu muDual
            S Sdual p pDual family familyDual schedule k padding length,
          data.extentX 0 = initialX /\
          data.extentY length = terminalY /\
          (forall j, initialX <= data.extentX j) /\
          forall j, terminalY <= data.extentY j := by
  obtain ⟨thresholdX, thresholdY, hthreshold⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  refine ⟨thresholdX, thresholdY, ?_⟩
  intro initialX terminalY hinitialX hterminalY
  let extentY : Nat -> Nat := fun j =>
    terminalY + 2 * padding * (length - j)
  let State (j : Nat) :=
    Sigma fun x : {x : Nat // initialX <= x} =>
      AlignedExactExtentPairedMixedBoundaryScores
        E Edual mu muDual S Sdual p pDual family familyDual schedule k x.1
          (extentY j)
  have hy (j : Nat) : thresholdY <= extentY j := by
    exact hterminalY.trans (by simp only [extentY]; omega)
  let initial : State 0 :=
    ⟨⟨initialX, le_rfl⟩, Classical.choice
      (hthreshold hinitialX (hy 0))⟩
  let nextState (j : Nat) (previous : State j) : State (j + 1) := by
    let span := previous.2.raw.wideRightInt -
      previous.2.raw.wideLeftInt
    have hspan : 0 <= span :=
      (show (0 : Int) <= previous.1.1 by omega).trans
        previous.2.raw.extentX_le_wideSpan
    let nextX := span.toNat + 2 * padding
    have hpreviousX : initialX <= previous.1.1 := previous.1.2
    have hnextX : initialX <= nextX := by
      have htoNat : previous.1.1 <= span.toNat := by
        rw [Int.le_toNat hspan]
        exact previous.2.raw.extentX_le_wideSpan
      exact hpreviousX.trans (htoNat.trans (Nat.le_add_right _ _))
    have hthresholdNext : thresholdX <= nextX :=
      hinitialX.trans hnextX
    exact ⟨⟨nextX, hnextX⟩, Classical.choice
      (hthreshold hthresholdNext (hy (j + 1)))⟩
  let state : forall j, State j := fun j =>
    Nat.rec (motive := State) initial nextState j
  let extentX : Nat -> Nat := fun j => (state j).1.1
  let level : forall j, AlignedExactExtentPairedMixedBoundaryScores
      E Edual mu muDual S Sdual p pDual family familyDual schedule k
        (extentX j) (extentY j) := fun j => (state j).2
  let data : AlignedCrossNestedPairedChain E Edual mu muDual
      S Sdual p pDual family familyDual schedule k padding length := {
    extentX := extentX
    extentY := extentY
    level := level
    nextX_eq := by
      intro j hj
      let span := (state j).2.raw.wideRightInt -
        (state j).2.raw.wideLeftInt
      have hspan : 0 <= span :=
        (show (0 : Int) <= (state j).1.1 by omega).trans
          (state j).2.raw.extentX_le_wideSpan
      change ((state (j + 1)).1.1 : Int) = span + 2 * (padding : Int)
      simp only [state, Nat.rec_add_one, nextState]
      change ((span.toNat + 2 * padding : Nat) : Int) =
        span + 2 * (padding : Int)
      push_cast
      rw [Int.toNat_of_nonneg hspan]
    nextY_eq := by
      intro j hj
      dsimp only [extentY]
      have hsub : length - j = length - (j + 1) + 1 := by omega
      rw [hsub]
      simp only [Nat.mul_add, Nat.mul_one]
      omega }
  refine ⟨data, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [data, extentY, Nat.sub_self, mul_zero, add_zero]
  · intro j
    exact (state j).1.2
  · intro j
    dsimp only [data, extentY]
    omega






theorem exists_alignedCrossNestedPairedChain_horizontalEnd_gt
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding length : Nat)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (lowerX lowerY : Nat) (hlowerX : 3 * B < 3 * (lowerX : Real))
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists data : AlignedCrossNestedPairedChain E Edual mu muDual
        S Sdual p pDual family familyDual schedule k padding length,
      (forall j, lowerX <= data.extentX j) /\
      (forall j, lowerY <= data.extentY j) /\
      1 - epsilon < mu.real (E.horizontalCrossingEvent 0
        (data.extentX length) 0 (data.extentY length)) := by
  obtain ⟨thresholdX, thresholdY, hchain⟩ :=
    exists_alignedCrossNestedPairedChain_at_endpoints
      E Edual mu muDual hTI hTIDual family familyDual schedule
        k padding length
  let initialX := max thresholdX lowerX
  let probeTerminalY := max thresholdY lowerY
  obtain ⟨probe, hprobeX, hprobeY, hprobeXLower, hprobeYLower⟩ :=
    hchain initialX probeTerminalY
      (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hterminalWidth : 3 * B <
      ((3 * (probe.extentX length : Int) : Int) : Real) := by
    have hlower : lowerX <= probe.extentX length :=
      (Nat.le_max_right _ _).trans (hprobeXLower length)
    push_cast
    have hlowerReal : (lowerX : Real) <= probe.extentX length := by
      exact_mod_cast hlower
    linarith
  obtain ⟨height, hheight, hcrossing⟩ :=
    E.exists_horizontalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique 0 B (-(probe.extentX length : Real))
        hB0 hB (3 * (probe.extentX length : Int)) hterminalWidth
        probeTerminalY hepsilon
  have hthresholdHeight : thresholdY <= height :=
    (Nat.le_max_left _ _).trans hheight
  obtain ⟨data, hdataX, hdataY, hdataXLower, hdataYLower⟩ :=
    hchain initialX height (Nat.le_max_left _ _) hthresholdHeight
  have hterminalX : probe.extentX length = data.extentX length := by
    apply probe.extentX_eq_of_zero_eq data
    · rw [hprobeX, hdataX]
    · exact le_rfl
  have hcrossing' : 1 - epsilon < mu.real
      (E.horizontalCrossingEvent 0 (probe.extentX length) 0 height) := by
    convert hcrossing using 1 <;> push_cast <;> ring
  refine ⟨data, ?_, ?_, ?_⟩
  · intro j
    exact (Nat.le_max_right _ _).trans (hdataXLower j)
  · intro j
    exact (Nat.le_max_right _ _).trans (hheight.trans (hdataYLower j))
  · rw [← hterminalX, hdataY]
    exact hcrossing'






theorem exists_alignedCrossNestedPairedChain_verticalStart_gt
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding length : Nat)
    (B : Real) (hB0 : 0 <= B)
    (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
    (lowerX lowerY : Nat) (hlowerY : 3 * B < 3 * (lowerY : Real))
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists data : AlignedCrossNestedPairedChain E Edual mu muDual
        S Sdual p pDual family familyDual schedule k padding length,
      (forall j, lowerX <= data.extentX j) /\
      (forall j, lowerY <= data.extentY j) /\
      1 - epsilon < mu.real (E.verticalCrossingEvent
        (data.level 0).raw.data.wideLeft
        (data.level 0).raw.data.wideRight 0 (data.extentY 0)) := by
  obtain ⟨thresholdX, thresholdY, hchain⟩ :=
    exists_alignedCrossNestedPairedChain_at_endpoints
      E Edual mu muDual hTI hTIDual family familyDual schedule
        k padding length
  let terminalY := max thresholdY lowerY
  let initialY := terminalY + 2 * padding * length
  have hinitialHeight : 3 * B <
      ((3 * (initialY : Int) : Int) : Real) := by
    have hlower : lowerY <= initialY := by
      exact (Nat.le_max_right _ _).trans (Nat.le_add_right _ _)
    push_cast
    have hlowerReal : (lowerY : Real) <= initialY := by
      exact_mod_cast hlower
    linarith
  obtain ⟨width, hwidth, hcrossing⟩ :=
    E.exists_verticalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique 0 B (-(initialY : Real)) hB0 hB
        (3 * (initialY : Int)) hinitialHeight (max thresholdX lowerX)
          hepsilon
  have hthresholdWidth : thresholdX <= width :=
    (Nat.le_max_left _ _).trans hwidth
  obtain ⟨data, hdataX, hdataY, hdataXLower, hdataYLower⟩ :=
    hchain width terminalY hthresholdWidth (Nat.le_max_left _ _)
  have hdataInitialY : data.extentY 0 = initialY := by
    rw [data.extentY_eq_terminal_add (j := 0) (by omega), hdataY]
    simp only [initialY, Nat.sub_zero]
  have hcrossing' : 1 - epsilon < mu.real
      (E.verticalCrossingEvent 0 width 0 initialY) := by
    convert hcrossing using 1 <;> push_cast <;> ring
  have hleft : (data.level 0).raw.data.wideLeft <= (0 : Real) :=
    (data.level 0).raw.data.wideLeft_le
  have hright : (width : Real) <=
      (data.level 0).raw.data.wideRight := by
    calc
      (width : Real) = data.extentX 0 := by exact_mod_cast hdataX.symm
      _ = (data.level 0).raw.data.narrowRight := by
        exact (data.level 0).raw.narrowRight_eq.symm
      _ <= (data.level 0).raw.data.wideRight :=
        (data.level 0).raw.data.narrowRight_le
  have hmono : E.verticalCrossingEvent 0 width 0 initialY <=
      E.verticalCrossingEvent
        (data.level 0).raw.data.wideLeft
        (data.level 0).raw.data.wideRight 0 initialY :=
    E.verticalCrossingEvent_mono_horizontal hleft hright
  have hwideCrossing : 1 - epsilon < mu.real
      (E.verticalCrossingEvent
        (data.level 0).raw.data.wideLeft
        (data.level 0).raw.data.wideRight 0 initialY) :=
    hcrossing'.trans_le (measureReal_mono hmono)
  refine ⟨data, ?_, ?_, ?_⟩
  · intro j
    exact (Nat.le_max_right _ _).trans (hwidth.trans (hdataXLower j))
  · intro j
    exact (Nat.le_max_right _ _).trans (hdataYLower j)
  · have hinitialYReal : (data.extentY 0 : Real) = initialY := by
      exact_mod_cast hdataInitialY
    rw [hinitialYReal]
    exact hwideCrossing






def opposedEndpointVerticalScore (width height : Nat) : Real :=
  if height < width then 1 else 0



def opposedEndpointHorizontalScore (width height : Nat) : Real :=
  if width < height then 1 else 0

theorem opposedEndpointVerticalScore_mono_width
    {width width' height : Nat} (hwidth : width <= width') :
    opposedEndpointVerticalScore width height <=
      opposedEndpointVerticalScore width' height := by
  unfold opposedEndpointVerticalScore
  split_ifs <;> norm_num <;> omega

theorem opposedEndpointVerticalScore_anti_height
    {width height height' : Nat} (hheight : height <= height') :
    opposedEndpointVerticalScore width height' <=
      opposedEndpointVerticalScore width height := by
  unfold opposedEndpointVerticalScore
  split_ifs <;> norm_num <;> omega

theorem opposedEndpointHorizontalScore_anti_width
    {width width' height : Nat} (hwidth : width <= width') :
    opposedEndpointHorizontalScore width' height <=
      opposedEndpointHorizontalScore width height := by
  unfold opposedEndpointHorizontalScore
  split_ifs <;> norm_num <;> omega

theorem opposedEndpointHorizontalScore_mono_height
    {width height height' : Nat} (hheight : height <= height') :
    opposedEndpointHorizontalScore width height <=
      opposedEndpointHorizontalScore width height' := by
  unfold opposedEndpointHorizontalScore
  split_ifs <;> norm_num <;> omega



theorem exists_opposedEndpointVerticalSelector
    (height minimumWidth : Nat -> Nat) :
    exists width : Nat -> Nat,
      (forall n, minimumWidth n <= width n) /\
      Tendsto (fun n => opposedEndpointVerticalScore (width n) (height n))
        atTop (nhds 1) := by
  let width : Nat -> Nat := fun n => max (minimumWidth n) (height n + 1)
  refine ⟨width, fun n => Nat.le_max_left _ _, ?_⟩
  have heq : (fun n => opposedEndpointVerticalScore (width n) (height n)) =
      fun _ : Nat => (1 : Real) := by
    funext n
    have hlt : height n < width n :=
      (Nat.lt_succ_self _).trans_le (Nat.le_max_right _ _)
    simp only [opposedEndpointVerticalScore, hlt, if_pos]
  rw [heq]
  exact tendsto_const_nhds




theorem exists_opposedEndpointHorizontalSelector
    (width minimumHeight : Nat -> Nat) :
    exists height : Nat -> Nat,
      (forall n, minimumHeight n <= height n) /\
      Tendsto (fun n => opposedEndpointHorizontalScore (width n) (height n))
        atTop (nhds 1) := by
  let height : Nat -> Nat := fun n => max (minimumHeight n) (width n + 1)
  refine ⟨height, fun n => Nat.le_max_left _ _, ?_⟩
  have heq : (fun n => opposedEndpointHorizontalScore (width n) (height n)) =
      fun _ : Nat => (1 : Real) := by
    funext n
    have hlt : width n < height n :=
      (Nat.lt_succ_self _).trans_le (Nat.le_max_right _ _)
    simp only [opposedEndpointHorizontalScore, hlt, if_pos]
  rw [heq]
  exact tendsto_const_nhds






theorem opposedEndpointScores_not_simultaneously_tendsto_one
    (width height : Nat -> Nat) :
    ¬ (Tendsto
      (fun n => opposedEndpointVerticalScore (width n) (height n))
        atTop (nhds 1) /\
      Tendsto
        (fun n => opposedEndpointHorizontalScore (width n) (height n))
          atTop (nhds 1)) := by
  rintro ⟨hvertical, hhorizontal⟩
  have hverticalEventually : ∀ᶠ n in atTop,
      (1 / 2 : Real) < opposedEndpointVerticalScore (width n) (height n) :=
    hvertical.eventually (Ioi_mem_nhds (by norm_num))
  have hhorizontalEventually : ∀ᶠ n in atTop,
      (1 / 2 : Real) < opposedEndpointHorizontalScore (width n) (height n) :=
    hhorizontal.eventually (Ioi_mem_nhds (by norm_num))
  obtain ⟨n, hv, hh⟩ :=
    (hverticalEventually.and hhorizontalEventually).exists
  by_cases hlt : height n < width n
  · have hnot : ¬ (width n < height n) := by omega
    simp only [opposedEndpointHorizontalScore, hnot] at hh
    norm_num at hh
  · simp only [opposedEndpointVerticalScore, hlt] at hv
    norm_num at hv



theorem exists_alignedCrossNestedPairedChain_ge
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding length lowerX lowerY : Nat) :
    exists data : AlignedCrossNestedPairedChain E Edual mu muDual
        S Sdual p pDual family familyDual schedule k padding length,
      (forall j, lowerX <= data.extentX j) /\
      (forall j, lowerY <= data.extentY j) := by
  obtain ⟨thresholdX0, thresholdY0, hthreshold0⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  let thresholdX := max thresholdX0 lowerX
  let thresholdY := max thresholdY0 lowerY
  have hthreshold {extentX extentY : Nat}
      (hx : thresholdX <= extentX) (hy : thresholdY <= extentY) :
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores
        E Edual mu muDual S Sdual p pDual family familyDual schedule k
          extentX extentY) :=
    hthreshold0 ((Nat.le_max_left _ _).trans hx)
      ((Nat.le_max_left _ _).trans hy)
  let extentY : Nat -> Nat := fun j =>
    thresholdY + 2 * padding * (length - j)
  let State (j : Nat) :=
    Sigma fun x : {x : Nat // thresholdX <= x} =>
      AlignedExactExtentPairedMixedBoundaryScores
        E Edual mu muDual S Sdual p pDual family familyDual schedule k x.1
          (extentY j)
  have hy (j : Nat) : thresholdY <= extentY j := by
    dsimp only [extentY]
    omega
  let initial : State 0 :=
    ⟨⟨thresholdX, le_rfl⟩, Classical.choice
      (hthreshold (extentX := thresholdX) (extentY := extentY 0)
        (le_refl _) (hy 0))⟩
  let nextState (j : Nat) (previous : State j) : State (j + 1) := by
    let span := previous.2.raw.wideRightInt -
      previous.2.raw.wideLeftInt
    have hspan : 0 <= span :=
      (show (0 : Int) <= previous.1.1 by omega).trans
        previous.2.raw.extentX_le_wideSpan
    let nextX := span.toNat + 2 * padding
    have hpreviousX : thresholdX <= previous.1.1 := previous.1.2
    have hnextX : thresholdX <= nextX := by
      have htoNat : previous.1.1 <= span.toNat := by
        rw [Int.le_toNat hspan]
        exact previous.2.raw.extentX_le_wideSpan
      exact hpreviousX.trans (htoNat.trans (Nat.le_add_right _ _))
    exact ⟨⟨nextX, hnextX⟩, Classical.choice
      (hthreshold (extentX := nextX) (extentY := extentY (j + 1))
        hnextX (hy (j + 1)))⟩
  let state : forall j, State j := fun j =>
    Nat.rec (motive := State) initial nextState j
  let extentX : Nat -> Nat := fun j => (state j).1.1
  let level : forall j, AlignedExactExtentPairedMixedBoundaryScores
      E Edual mu muDual S Sdual p pDual family familyDual schedule k
        (extentX j) (extentY j) := fun j => (state j).2
  refine ⟨{
    extentX := extentX
    extentY := extentY
    level := level
    nextX_eq := ?_
    nextY_eq := ?_ }, ?_, ?_⟩
  · intro j hj
    let span := (state j).2.raw.wideRightInt -
      (state j).2.raw.wideLeftInt
    have hspan : 0 <= span :=
      (show (0 : Int) <= (state j).1.1 by omega).trans
        (state j).2.raw.extentX_le_wideSpan
    change ((state (j + 1)).1.1 : Int) = span + 2 * (padding : Int)
    simp only [state, Nat.rec_add_one, nextState]
    change ((span.toNat + 2 * padding : Nat) : Int) =
      span + 2 * (padding : Int)
    push_cast
    rw [Int.toNat_of_nonneg hspan]
  · intro j hj
    dsimp only [extentY]
    have hsub : length - j = length - (j + 1) + 1 := by omega
    rw [hsub]
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  · intro j
    exact (Nat.le_max_right _ _).trans (state j).1.2
  · intro j
    exact (Nat.le_max_right _ _).trans (hy j)


theorem nonempty_alignedCrossNestedPairedChain
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding length : Nat) :
    Nonempty (AlignedCrossNestedPairedChain E Edual mu muDual
      S Sdual p pDual family familyDual schedule k padding length) := by
  obtain ⟨data, _, _⟩ := exists_alignedCrossNestedPairedChain_ge
    E Edual mu muDual hTI hTIDual family familyDual schedule
      k padding length 0 0
  exact ⟨data⟩




structure PairedAdjacentCrossNestedOutwardArrayData
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    {step : Nat -> Int}
    (scheduleData : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step)
    (padding : Nat) (K : Nat -> Nat) where
  dualRadius : Nat -> Nat
  dualOutward :
    forall (k extentX extentY : Nat -> Nat)
      (exact : forall n, AlignedExactExtentPairedMixedBoundaryScores
        E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
        (scheduleData.score n) (scheduleData.scoreDual n)
        (scheduleData.family n) (scheduleData.familyDual n)
        (scheduleData.schedule n) (k n) (extentX n) (extentY n)),
      (forall n, PairedAlignedConnectorSlack E Edual
        (scheduleData.family n) (scheduleData.familyDual n)
        (scheduleData.schedule n) (max (dualRadius n) n) (k n)) ->
      Tendsto (fun n => max
        (muDual.real (Edual.verticalCrossingEvent
          (exact n).raw.data.wideLeft (exact n).raw.data.wideRight
          0 (extentY n)))
        (muDual.real (Edual.horizontalCrossingEvent
          0 (extentX n) 0 (extentY n)))) atTop (nhds 1)
  index : Nat -> Nat
  slack : forall n, PairedAlignedConnectorSlack E Edual
    (scheduleData.family n) (scheduleData.familyDual n)
    (scheduleData.schedule n)
    (max (max (scheduleData.radius n) (dualRadius n)) n) (index n)
  chain : forall n, AlignedCrossNestedPairedChain E Edual mu muDual
    (P.orbitBox n) (Pdual.orbitBox n)
    (scheduleData.score n) (scheduleData.scoreDual n)
    (scheduleData.family n) (scheduleData.familyDual n)
    (scheduleData.schedule n) (index n) padding (2 * (K n + 1) + 2)



theorem PairedAdjacentBoundaryBandScheduleData.exists_crossNestedOutwardArrayData
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {step : Nat -> Int}
    (scheduleData : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step)
    (hTI : P.IsTranslationInvariant mu)
    (hFKGDual : IsFKG muDual)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (padding : Nat) (K lowerX lowerY : Nat -> Nat) :
    exists data : PairedAdjacentCrossNestedOutwardArrayData
        E Edual mu muDual scheduleData padding K,
      (forall n j, lowerX n <= (data.chain n).extentX j) /\
      (forall n j, lowerY n <= (data.chain n).extentY j) := by
  obtain ⟨dualRadius, hdual⟩ :=
    scheduleData.exists_alignedExact_dualOutwardRadius
      hFKGDual hTIDual huniqueDual (fun _ => 0) (fun _ => le_rfl)
  have hslack (n : Nat) := exists_pairedAlignedConnectorSlack E Edual
    (scheduleData.family n) (scheduleData.familyDual n)
    (scheduleData.schedule n)
    (max (max (scheduleData.radius n) (dualRadius n)) n)
  let index : Nat -> Nat := fun n => Classical.choose (hslack n)
  let slack : forall n, PairedAlignedConnectorSlack E Edual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n)
      (max (max (scheduleData.radius n) (dualRadius n)) n)
      (index n) := fun n => Classical.choose_spec (hslack n)
  have hchain (n : Nat) := exists_alignedCrossNestedPairedChain_ge
    E Edual mu muDual hTI hTIDual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n) (index n) padding (2 * (K n + 1) + 2)
      (lowerX n) (lowerY n)
  let chain : forall n, AlignedCrossNestedPairedChain E Edual mu muDual
      (P.orbitBox n) (Pdual.orbitBox n)
      (scheduleData.score n) (scheduleData.scoreDual n)
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n) (index n) padding
        (2 * (K n + 1) + 2) := fun n => Classical.choose (hchain n)
  have hdual' :
      forall (k extentX extentY : Nat -> Nat)
        (exact : forall n, AlignedExactExtentPairedMixedBoundaryScores
          E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n)
          (scheduleData.score n) (scheduleData.scoreDual n)
          (scheduleData.family n) (scheduleData.familyDual n)
          (scheduleData.schedule n) (k n) (extentX n) (extentY n)),
        (forall n, PairedAlignedConnectorSlack E Edual
          (scheduleData.family n) (scheduleData.familyDual n)
          (scheduleData.schedule n) (max (dualRadius n) n) (k n)) ->
        Tendsto (fun n => max
          (muDual.real (Edual.verticalCrossingEvent
            (exact n).raw.data.wideLeft (exact n).raw.data.wideRight
            0 (extentY n)))
          (muDual.real (Edual.horizontalCrossingEvent
            0 (extentX n) 0 (extentY n)))) atTop (nhds 1) := by
    intro k extentX extentY exact hslackDual
    simpa only [Int.cast_zero, sub_zero, add_zero] using
      hdual k extentX extentY exact hslackDual
  let data : PairedAdjacentCrossNestedOutwardArrayData
      E Edual mu muDual scheduleData padding K := {
    dualRadius := dualRadius
    dualOutward := hdual'
    index := index
    slack := slack
    chain := chain }
  refine ⟨data, ?_, ?_⟩
  · intro n j
    exact (Classical.choose_spec (hchain n)).1 j
  · intro n j
    exact (Classical.choose_spec (hchain n)).2 j



theorem PairedAdjacentCrossNestedOutwardArrayData.even_odd_local_limits
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {step : Nat -> Int}
    {scheduleData : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step}
    {padding : Nat} {K : Nat -> Nat}
    (data : PairedAdjacentCrossNestedOutwardArrayData
      E Edual mu muDual scheduleData padding K)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    (forall k : Nat -> Nat, Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent 0
        ((data.chain n).extentX (2 * k n + 2)) 0
        ((data.chain n).extentY (2 * k n + 2))))
      (mu.real (E.verticalCrossingEvent
        ((data.chain n).level (2 * k n + 2)).raw.data.wideLeft
        ((data.chain n).level (2 * k n + 2)).raw.data.wideRight 0
        (((data.chain n).extentY (2 * k n + 2)) +
          (step n).toNat))))
      atTop (nhds 1)) /\
    (forall k : Nat -> Nat, Tendsto (fun n => max
      (muDual.real (Edual.verticalCrossingEvent
        ((data.chain n).level (2 * k n + 1)).raw.data.wideLeft
        ((data.chain n).level (2 * k n + 1)).raw.data.wideRight 0
        ((data.chain n).extentY (2 * k n + 1))))
      (muDual.real (Edual.horizontalCrossingEvent 0
        ((data.chain n).extentX (2 * k n + 1)) 0
        ((data.chain n).extentY (2 * k n + 1))))) atTop (nhds 1)) := by
  have hprimalSlack : forall n, PairedAlignedConnectorSlack E Edual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n)
      (max (scheduleData.radius n) n) (data.index n) := by
    intro n
    apply (data.slack n).restrictRadius E Edual
    omega
  have hdualSlack : forall n, PairedAlignedConnectorSlack E Edual
      (scheduleData.family n) (scheduleData.familyDual n)
      (scheduleData.schedule n)
      (max (data.dualRadius n) n) (data.index n) := by
    intro n
    apply (data.slack n).restrictRadius E Edual
    omega
  constructor
  · intro k
    exact scheduleData.alignedExact_primalAdjacent_limit hFKG hTI hunique
      data.index (fun n => (data.chain n).extentX (2 * k n + 2))
      (fun n => (data.chain n).extentY (2 * k n + 2))
      (fun n => (data.chain n).level (2 * k n + 2)) hprimalSlack
  · intro k
    exact data.dualOutward data.index
      (fun n => (data.chain n).extentX (2 * k n + 1))
      (fun n => (data.chain n).extentY (2 * k n + 1))
      (fun n => (data.chain n).level (2 * k n + 1)) hdualSlack



theorem AlignedExactExtentPairedMixedBoundaryScores.shifted_matched_pair
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : D.primalEmbedding.NormalBoundaryBandFamily mu S p}
    {familyDual : D.dualEmbedding.NormalBoundaryBandFamily
      (D.dualMeasure mu) Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    {schedule : PairedAlignedMarginSchedule D.primalEmbedding
      D.dualEmbedding family familyDual
      verticalRequirement horizontalRequirement}
    {k lowerX lowerY upperX upperY padding : Nat}
    (lower : AlignedExactExtentPairedMixedBoundaryScores
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      S Sdual p pDual family familyDual schedule k lowerX lowerY)
    (upper : AlignedExactExtentPairedMixedBoundaryScores
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      S Sdual p pDual family familyDual schedule k upperX upperY)
    (hnextX : (upperX : Int) = lower.raw.wideRightInt -
      lower.raw.wideLeftInt + 2 * padding)
    (hnextY : lowerY = upperY + 2 * padding)
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (hpadding : 4 * B <= (padding : Real))
    (hlowerX : 10 * B < lowerX) (hlowerY : 10 * B < lowerY)
    (hupperX : 10 * B < upperX) (hupperY : 10 * B < upperY) :
    mu.real (D.primalEmbedding.horizontalCrossingEvent
        0 upperX 0 upperY) +
      (D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
        lower.raw.data.wideLeft lower.raw.data.wideRight 0 lowerY) <= 1 /\
    mu.real (D.primalEmbedding.verticalCrossingEvent
        lower.raw.data.wideLeft lower.raw.data.wideRight 0 lowerY) +
      (D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
        0 upperX 0 upperY) <= 1 := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  constructor
  · let z : Site 2 := fun i => if i = 0 then
      padding - lower.raw.wideLeftInt else -(padding : Int)
    have hupperXR : (upperX : Real) =
        (lower.raw.wideRightInt : Real) - lower.raw.wideLeftInt +
          2 * padding := by
      exact_mod_cast hnextX
    have hlowerYR : (lowerY : Real) = upperY + 2 * padding := by
      exact_mod_cast hnextY
    have hspanX : (0 : Real) + 5 * B < upperX - 5 * B := by
      linarith
    have hspanY : -(padding : Real) + 5 * B <
        upperY + padding - 5 * B := by
      linarith
    have hbase := D.matchedCrossing_measureReal_add_le_one_of_pads
      mu hBpos hBp hBd hpadding hpadding hspanX hspanY
    have htranslated :=
      D.dualEmbedding.verticalCrossing_translate_measureReal_le
        (D.dualMeasure mu) hTIDual z lower.raw.data.wideLeft
        lower.raw.data.wideRight 0 lowerY
    have hdualLe :
        (D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
            lower.raw.data.wideLeft lower.raw.data.wideRight 0 lowerY) <=
          (D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
            padding (upperX - padding) (-padding) (upperY + padding)) := by
      calc
        _ <= (D.dualMeasure mu).real
            (D.dualEmbedding.verticalCrossingEvent
              (lower.raw.data.wideLeft + (z 0 : Real))
              (lower.raw.data.wideRight + (z 0 : Real))
              (0 + (z 1 : Real)) (lowerY + (z 1 : Real))) := htranslated
        _ = _ := by
          apply congrArg (fun event : Set (ConfigSpace (Sym2 W)) =>
            (D.dualMeasure mu).real event)
          congr 1
          all_goals simp only [z, Pi.zero_apply, if_pos, if_neg]
          · rw [lower.raw.wideLeft_eq]
            push_cast
            ring
          · rw [lower.raw.wideRight_eq]
            push_cast
            linarith [hupperXR]
          · push_cast
            ring
          · push_cast
            linarith [hlowerYR]
    simp_rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)] at hdualLe
    have hbase' :
        mu.real (D.primalEmbedding.horizontalCrossingEvent
            0 upperX 0 upperY) +
          mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
            D.dualEmbedding.verticalCrossingEvent
              padding (upperX - padding) (-padding) (upperY + padding)) <=
            1 := by
      simpa only [zero_add, neg_add_cancel, add_sub_cancel_right,
        sub_add_cancel] using hbase
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
    linarith
  · let z : Site 2 := fun i => if i = 0 then
      lower.raw.wideLeftInt - padding else (padding : Int)
    have hupperXR : (upperX : Real) =
        (lower.raw.wideRightInt : Real) - lower.raw.wideLeftInt +
          2 * padding := by
      exact_mod_cast hnextX
    have hlowerYR : (lowerY : Real) = upperY + 2 * padding := by
      exact_mod_cast hnextY
    have hwideSpan : (lowerX : Real) <=
        lower.raw.wideRightInt - lower.raw.wideLeftInt := by
      exact_mod_cast lower.raw.extentX_le_wideSpan
    have hspanX : lower.raw.data.wideLeft - padding + 5 * B <
        lower.raw.data.wideRight + padding - 5 * B := by
      rw [lower.raw.wideLeft_eq, lower.raw.wideRight_eq]
      push_cast
      have hpad0 : (0 : Real) <= padding := by positivity
      linarith
    have hspanY : (0 : Real) + 5 * B < lowerY - 5 * B := by
      linarith
    have hbase :=
      D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads
        mu hBpos hBp hBd hpadding hpadding hspanX hspanY
    have htranslated :=
      D.dualEmbedding.horizontalCrossing_translate_measureReal_le
        (D.dualMeasure mu) hTIDual z 0 upperX 0 upperY
    have hdualLe :
        (D.dualMeasure mu).real
            (D.dualEmbedding.horizontalCrossingEvent 0 upperX 0 upperY) <=
          (D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
            (lower.raw.data.wideLeft - padding)
            (lower.raw.data.wideRight + padding)
            padding (lowerY - padding)) := by
      calc
        _ <= (D.dualMeasure mu).real
            (D.dualEmbedding.horizontalCrossingEvent
              (0 + (z 0 : Real)) (upperX + (z 0 : Real))
              (0 + (z 1 : Real)) (upperY + (z 1 : Real))) := htranslated
        _ = _ := by
          apply congrArg (fun event : Set (ConfigSpace (Sym2 W)) =>
            (D.dualMeasure mu).real event)
          congr 1
          all_goals simp only [z, Pi.zero_apply, if_pos, if_neg]
          · rw [lower.raw.wideLeft_eq]
            push_cast
            ring
          · rw [lower.raw.wideRight_eq]
            push_cast
            linarith [hupperXR]
          · push_cast
            ring
          · push_cast
            linarith [hlowerYR]
    simp_rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)] at hdualLe
    have hbase' :
        mu.real (D.primalEmbedding.verticalCrossingEvent
            lower.raw.data.wideLeft lower.raw.data.wideRight 0 lowerY) +
          mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
            D.dualEmbedding.horizontalCrossingEvent
              (lower.raw.data.wideLeft - padding)
              (lower.raw.data.wideRight + padding)
              padding (lowerY - padding)) <= 1 := by
      simpa only [zero_add, add_sub_cancel_right, sub_add_cancel] using hbase
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
    linarith




theorem PairedAdjacentCrossNestedOutwardArrayData.false_of_endpoints
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {scheduleData : PairedAdjacentBoundaryBandScheduleData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) (fun _ => 0)}
    {padding : Nat} {K : Nat -> Nat}
    (data : PairedAdjacentCrossNestedOutwardArrayData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      scheduleData padding K)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (hpadding : 4 * B <= (padding : Real))
    (hextentX : forall n j, 10 * B < (data.chain n).extentX j)
    (hextentY : forall n j, 10 * B < (data.chain n).extentY j)
    (hverticalStart : Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        ((data.chain n).level 0).raw.data.wideLeft
        ((data.chain n).level 0).raw.data.wideRight 0
        ((data.chain n).extentY 0))) atTop (nhds 1))
    (hhorizontalEnd : Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent 0
        ((data.chain n).extentX (2 * (K n + 1) + 2)) 0
        ((data.chain n).extentY (2 * (K n + 1) + 2))))
      atTop (nhds 1)) : False := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  let horizontal : Nat -> Nat -> Real := fun n j => mu.real
    (D.primalEmbedding.horizontalCrossingEvent 0
      ((data.chain n).extentX j) 0 ((data.chain n).extentY j))
  let vertical : Nat -> Nat -> Real := fun n j => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      ((data.chain n).level j).raw.data.wideLeft
      ((data.chain n).level j).raw.data.wideRight 0
      ((data.chain n).extentY j))
  let dualVertical : Nat -> Nat -> Real := fun n j =>
    (D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
      ((data.chain n).level j).raw.data.wideLeft
      ((data.chain n).level j).raw.data.wideRight 0
      ((data.chain n).extentY j))
  let dualHorizontal : Nat -> Nat -> Real := fun n j =>
    (D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent 0
      ((data.chain n).extentX j) 0 ((data.chain n).extentY j))
  obtain ⟨hprimal, hdual⟩ :=
    data.even_odd_local_limits hFKG hTI hunique
  apply shifted_crossNested_array_contradiction_of_bounded_limits
    horizontal vertical dualVertical dualHorizontal K
  · intro n j
    exact measureReal_nonneg
  · intro n j
    exact measureReal_nonneg
  · intro n j
    exact measureReal_le_one
  · intro n j
    exact measureReal_le_one
  · simpa only [vertical, mul_zero] using hverticalStart
  · simpa only [horizontal] using hhorizontalEnd
  · intro n j hj
    have hpair :=
      AlignedExactExtentPairedMixedBoundaryScores.shifted_matched_pair
      D mu ((data.chain n).level j) ((data.chain n).level (j + 1))
      ((data.chain n).nextX_eq j hj) ((data.chain n).nextY_eq j hj)
      hTIDual B hBpos hBp hBd hpadding
      (hextentX n j) (hextentY n j)
      (hextentX n (j + 1)) (hextentY n (j + 1))
    simpa only [horizontal, dualVertical] using hpair.1
  · intro n j hj
    have hpair :=
      AlignedExactExtentPairedMixedBoundaryScores.shifted_matched_pair
      D mu ((data.chain n).level j) ((data.chain n).level (j + 1))
      ((data.chain n).nextX_eq j hj) ((data.chain n).nextY_eq j hj)
      hTIDual B hBpos hBp hBd hpadding
      (hextentX n j) (hextentY n j)
      (hextentX n (j + 1)) (hextentY n (j + 1))
    simpa only [vertical, dualHorizontal] using hpair.2
  · intro k hk
    have hlim := hprimal k
    simpa only [horizontal, vertical, Int.toNat_zero, Nat.cast_zero,
      add_zero] using hlim
  · intro k hk
    simpa only [dualVertical, dualHorizontal] using hdual k





structure PeriodicPlanarDualPair.CrossNestedOutwardArrayPreparation
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  B : Real
  Bpos : 0 < B
  primalArcBound : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t -
        D.primalEmbedding.vertex x) i| <= B
  dualArcBound : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t -
        D.dualEmbedding.vertex x) i| <= B
  padding : Nat
  padding_ge : 4 * B <= (padding : Real)
  scheduleData : PairedAdjacentBoundaryBandScheduleData
    D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) (fun _ => 0)
  array : PairedAdjacentCrossNestedOutwardArrayData
    D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      scheduleData padding (fun n => n)
  extentX_large : forall n j, 10 * B < (array.chain n).extentX j
  extentY_large : forall n j, 10 * B < (array.chain n).extentY j




theorem PeriodicPlanarDualPair.CrossNestedOutwardArrayPreparation.exists_horizontalEndpoint_rebuild
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (preparation : D.CrossNestedOutwardArrayPreparation mu)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu)) :
    exists rebuilt : D.CrossNestedOutwardArrayPreparation mu,
      Tendsto (fun n => mu.real
        (D.primalEmbedding.horizontalCrossingEvent 0
          ((rebuilt.array.chain n).extentX (2 * (n + 1) + 2)) 0
          ((rebuilt.array.chain n).extentY (2 * (n + 1) + 2))))
        atTop (nhds 1) := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  obtain ⟨lower, hlower⟩ := exists_nat_gt (10 * preparation.B)
  have hthree : 3 * preparation.B < 3 * (lower : Real) := by
    linarith
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  have hrow (n : Nat) :=
    exists_alignedCrossNestedPairedChain_horizontalEnd_gt
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      hFKG hTI hunique hTIDual
      (preparation.scheduleData.family n)
      (preparation.scheduleData.familyDual n)
      (preparation.scheduleData.schedule n)
      (preparation.array.index n) preparation.padding (2 * (n + 1) + 2)
      preparation.B preparation.Bpos.le preparation.primalArcBound
      lower lower hthree (hepsilon n)
  let chain : forall n, AlignedCrossNestedPairedChain
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      (P.orbitBox n) (Pdual.orbitBox n)
      (preparation.scheduleData.score n)
      (preparation.scheduleData.scoreDual n)
      (preparation.scheduleData.family n)
      (preparation.scheduleData.familyDual n)
      (preparation.scheduleData.schedule n)
      (preparation.array.index n) preparation.padding (2 * (n + 1) + 2) :=
    fun n => Classical.choose (hrow n)
  let array : PairedAdjacentCrossNestedOutwardArrayData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      preparation.scheduleData preparation.padding (fun n => n) := {
    dualRadius := preparation.array.dualRadius
    dualOutward := preparation.array.dualOutward
    index := preparation.array.index
    slack := preparation.array.slack
    chain := chain }
  have hlargeX : forall n j, 10 * preparation.B <
      (array.chain n).extentX j := by
    intro n j
    have hle : lower <= (array.chain n).extentX j :=
      (Classical.choose_spec (hrow n)).1 j
    exact hlower.trans_le (by exact_mod_cast hle)
  have hlargeY : forall n j, 10 * preparation.B <
      (array.chain n).extentY j := by
    intro n j
    have hle : lower <= (array.chain n).extentY j :=
      (Classical.choose_spec (hrow n)).2.1 j
    exact hlower.trans_le (by exact_mod_cast hle)
  let rebuilt : D.CrossNestedOutwardArrayPreparation mu := {
    B := preparation.B
    Bpos := preparation.Bpos
    primalArcBound := preparation.primalArcBound
    dualArcBound := preparation.dualArcBound
    padding := preparation.padding
    padding_ge := preparation.padding_ge
    scheduleData := preparation.scheduleData
    array := array
    extentX_large := hlargeX
    extentY_large := hlargeY }
  have hlowerLimit : Tendsto (fun n => 1 - epsilon n)
      atTop (nhds 1) := by
    have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
      simpa only [epsilon] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  refine ⟨rebuilt, tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlowerLimit tendsto_const_nhds ?_ (fun _ => measureReal_le_one)⟩
  intro n
  exact le_of_lt (Classical.choose_spec (hrow n)).2.2




theorem PeriodicPlanarDualPair.CrossNestedOutwardArrayPreparation.exists_verticalEndpoint_rebuild_at_error
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (preparation : D.CrossNestedOutwardArrayPreparation mu)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (epsilon : Nat -> Real) (hepsilon : forall n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (nhds 0)) :
    exists rebuilt : D.CrossNestedOutwardArrayPreparation mu,
      (forall n, 1 - epsilon n < mu.real
        (D.primalEmbedding.verticalCrossingEvent
          ((rebuilt.array.chain n).level 0).raw.data.wideLeft
          ((rebuilt.array.chain n).level 0).raw.data.wideRight 0
          ((rebuilt.array.chain n).extentY 0))) /\
      Tendsto (fun n => mu.real
        (D.primalEmbedding.verticalCrossingEvent
          ((rebuilt.array.chain n).level 0).raw.data.wideLeft
          ((rebuilt.array.chain n).level 0).raw.data.wideRight 0
          ((rebuilt.array.chain n).extentY 0))) atTop (nhds 1) := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  obtain ⟨lower, hlower⟩ := exists_nat_gt (10 * preparation.B)
  have hthree : 3 * preparation.B < 3 * (lower : Real) := by
    linarith
  have hrow (n : Nat) :=
    exists_alignedCrossNestedPairedChain_verticalStart_gt
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      hFKG hTI hunique hTIDual
      (preparation.scheduleData.family n)
      (preparation.scheduleData.familyDual n)
      (preparation.scheduleData.schedule n)
      (preparation.array.index n) preparation.padding (2 * (n + 1) + 2)
      preparation.B preparation.Bpos.le preparation.primalArcBound
      lower lower hthree (hepsilon n)
  let chain : forall n, AlignedCrossNestedPairedChain
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      (P.orbitBox n) (Pdual.orbitBox n)
      (preparation.scheduleData.score n)
      (preparation.scheduleData.scoreDual n)
      (preparation.scheduleData.family n)
      (preparation.scheduleData.familyDual n)
      (preparation.scheduleData.schedule n)
      (preparation.array.index n) preparation.padding (2 * (n + 1) + 2) :=
    fun n => Classical.choose (hrow n)
  let array : PairedAdjacentCrossNestedOutwardArrayData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      preparation.scheduleData preparation.padding (fun n => n) := {
    dualRadius := preparation.array.dualRadius
    dualOutward := preparation.array.dualOutward
    index := preparation.array.index
    slack := preparation.array.slack
    chain := chain }
  have hlargeX : forall n j, 10 * preparation.B <
      (array.chain n).extentX j := by
    intro n j
    have hle : lower <= (array.chain n).extentX j :=
      (Classical.choose_spec (hrow n)).1 j
    exact hlower.trans_le (by exact_mod_cast hle)
  have hlargeY : forall n j, 10 * preparation.B <
      (array.chain n).extentY j := by
    intro n j
    have hle : lower <= (array.chain n).extentY j :=
      (Classical.choose_spec (hrow n)).2.1 j
    exact hlower.trans_le (by exact_mod_cast hle)
  let rebuilt : D.CrossNestedOutwardArrayPreparation mu := {
    B := preparation.B
    Bpos := preparation.Bpos
    primalArcBound := preparation.primalArcBound
    dualArcBound := preparation.dualArcBound
    padding := preparation.padding
    padding_ge := preparation.padding_ge
    scheduleData := preparation.scheduleData
    array := array
    extentX_large := hlargeX
    extentY_large := hlargeY }
  have hlowerLimit : Tendsto (fun n => 1 - epsilon n)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  have hpointwise : forall n, 1 - epsilon n < mu.real
      (D.primalEmbedding.verticalCrossingEvent
        ((rebuilt.array.chain n).level 0).raw.data.wideLeft
        ((rebuilt.array.chain n).level 0).raw.data.wideRight 0
        ((rebuilt.array.chain n).extentY 0)) := fun n =>
    (Classical.choose_spec (hrow n)).2.2
  refine ⟨rebuilt, hpointwise,
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlowerLimit tendsto_const_nhds (fun n => le_of_lt (hpointwise n))
        (fun _ => measureReal_le_one)⟩



theorem PeriodicPlanarDualPair.CrossNestedOutwardArrayPreparation.exists_verticalEndpoint_rebuild
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (preparation : D.CrossNestedOutwardArrayPreparation mu)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu)) :
    exists rebuilt : D.CrossNestedOutwardArrayPreparation mu,
      Tendsto (fun n => mu.real
        (D.primalEmbedding.verticalCrossingEvent
          ((rebuilt.array.chain n).level 0).raw.data.wideLeft
          ((rebuilt.array.chain n).level 0).raw.data.wideRight 0
          ((rebuilt.array.chain n).extentY 0))) atTop (nhds 1) := by
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real)
  obtain ⟨rebuilt, _hlower, hlimit⟩ :=
    preparation.exists_verticalEndpoint_rebuild_at_error D mu
      hFKG hTI hunique hTIDual epsilon (fun n => by
        dsimp only [epsilon]
        positivity) (by
        simpa only [epsilon] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)))
  exact ⟨rebuilt, hlimit⟩



theorem PeriodicPlanarDualPair.nonempty_crossNestedOutwardArrayPreparation
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hFKGDual : IsFKG (D.dualMeasure mu))
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
    (huniqueDual : (D.dualMeasure mu)
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :
    Nonempty (D.CrossNestedOutwardArrayPreparation mu) := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  obtain ⟨Bp, hBp0, hBp⟩ :=
    D.primalEmbedding.exists_edgeArc_displacement_bound
  obtain ⟨Bd, hBd0, hBd⟩ :=
    D.dualEmbedding.exists_edgeArc_displacement_bound
  let B := max Bp Bd + 1
  have hBpos : 0 < B := by
    dsimp only [B]
    have hmax0 : 0 <= max Bp Bd := hBp0.trans (le_max_left _ _)
    linarith
  have hBp' : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B := by
    intro x y hxy t i
    exact (hBp hxy t i).trans (by dsimp only [B]; linarith [le_max_left Bp Bd])
  have hBd' : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B := by
    intro x y hxy t i
    exact (hBd hxy t i).trans (by dsimp only [B]; linarith [le_max_right Bp Bd])
  obtain ⟨padding, hpaddingStrict⟩ := exists_nat_gt (4 * B)
  have hpadding : 4 * B <= (padding : Real) := hpaddingStrict.le
  obtain ⟨lower, hlower⟩ := exists_nat_gt (10 * B)
  let scheduleData := Classical.choice
    (exists_pairedAdjacentBoundaryBandScheduleData
      D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      hFKG hTI hunique hFKGDual hTIDual huniqueDual
      (fun _ => 0) (fun _ => le_rfl))
  obtain ⟨array, hlargeX, hlargeY⟩ :=
    scheduleData.exists_crossNestedOutwardArrayData hTI hFKGDual hTIDual
      huniqueDual padding (fun n => n) (fun _ => lower) (fun _ => lower)
  exact ⟨{
    B := B
    Bpos := hBpos
    primalArcBound := hBp'
    dualArcBound := hBd'
    padding := padding
    padding_ge := hpadding
    scheduleData := scheduleData
    array := array
    extentX_large := fun n j => hlower.trans_le (by
      exact_mod_cast hlargeX n j)
    extentY_large := fun n j => hlower.trans_le (by
      exact_mod_cast hlargeY n j) }⟩



theorem PeriodicPlanarDualPair.exists_canonicalCrossNestedOutwardArrayPreparation_of_common
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hcommon :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    Nonempty (D.CrossNestedOutwardArrayPreparation mu) := by
  dsimp only
  letI : IsProbabilityMeasure
      (D.dualMeasure
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V)))) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  have hdata := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  exact D.nonempty_crossNestedOutwardArrayPreparation _
    hdata.1 hdata.2.1 hdata.2.2.2.2.1
    hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.2




structure PeriodicPlanarDualPair.CrossNestedOutwardEndpointCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  preparation : D.CrossNestedOutwardArrayPreparation mu
  verticalStart : Tendsto (fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      ((preparation.array.chain n).level 0).raw.data.wideLeft
      ((preparation.array.chain n).level 0).raw.data.wideRight 0
      ((preparation.array.chain n).extentY 0))) atTop (nhds 1)
  horizontalEnd : Tendsto (fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent 0
      ((preparation.array.chain n).extentX (2 * (n + 1) + 2)) 0
      ((preparation.array.chain n).extentY (2 * (n + 1) + 2))))
    atTop (nhds 1)


theorem PeriodicPlanarDualPair.CrossNestedOutwardEndpointCertificate.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (data : D.CrossNestedOutwardEndpointCertificate mu)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu)) : False := by
  exact data.preparation.array.false_of_endpoints D mu
    hFKG hTI hunique hTIDual data.preparation.B data.preparation.Bpos
    data.preparation.primalArcBound data.preparation.dualArcBound
    data.preparation.padding_ge data.preparation.extentX_large
    data.preparation.extentY_large data.verticalStart data.horizontalEnd



theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_crossNestedOutwardEndpointCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hcertificate :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        Nonempty (D.CrossNestedOutwardEndpointCertificate mu)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only
  intro hcommon
  letI : IsProbabilityMeasure
      (D.dualMeasure
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V)))) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  have hmodel := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  obtain ⟨data⟩ := hcertificate hcommon
  exact data.false D _ hmodel.1 hmodel.2.1 hmodel.2.2.2.2.1
    hmodel.2.2.2.1

end StatMech.FK.PeriodicPlanar
