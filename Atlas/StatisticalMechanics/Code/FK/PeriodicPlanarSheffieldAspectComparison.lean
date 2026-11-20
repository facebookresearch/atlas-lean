/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint
import Code.FK.PeriodicPlanarCrossingGluing
import Code.FK.PeriodicPlanarStrictCriticalAssembly
import Code.FK.PeriodicPlanarStrictNoCoexistenceClosure










open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}






theorem PeriodicPlaneEmbedding.horizontalCrossing_translate_measureReal_eq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    (a b c d : Real) :
    mu.real (E.horizontalCrossingEvent
      (a + (z 0 : Real)) (b + (z 0 : Real))
      (c + (z 1 : Real)) (d + (z 1 : Real))) =
      mu.real (E.horizontalCrossingEvent a b c d) := by
  apply le_antisymm
  · have h := E.horizontalCrossing_translate_measureReal_le
      mu hTI (-z) (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))
    simpa using h
  · exact E.horizontalCrossing_translate_measureReal_le
      mu hTI z a b c d



theorem PeriodicPlaneEmbedding.verticalCrossing_translate_measureReal_eq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    (a b c d : Real) :
    mu.real (E.verticalCrossingEvent
      (a + (z 0 : Real)) (b + (z 0 : Real))
      (c + (z 1 : Real)) (d + (z 1 : Real))) =
      mu.real (E.verticalCrossingEvent a b c d) := by
  apply le_antisymm
  · have h := E.verticalCrossing_translate_measureReal_le
      mu hTI (-z) (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))
    simpa using h
  · exact E.verticalCrossing_translate_measureReal_le
      mu hTI z a b c d



theorem PeriodicPlaneEmbedding.verticalCrossing_measureReal_le_translate_enlarge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    {a b a' b' c d : Real}
    (ha : a' <= a + (z 0 : Real)) (hb : b + (z 0 : Real) <= b') :
    mu.real (E.verticalCrossingEvent a b c d) <=
      mu.real (E.verticalCrossingEvent a' b'
        (c + (z 1 : Real)) (d + (z 1 : Real))) := by
  rw [<- E.verticalCrossing_translate_measureReal_eq mu hTI z a b c d]
  exact measureReal_mono
    (E.verticalCrossingEvent_mono_horizontal ha hb)



theorem PeriodicPlaneEmbedding.horizontalCrossing_measureReal_le_translate_enlarge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    {a b c d c' d' : Real}
    (hc : c' <= c + (z 1 : Real)) (hd : d + (z 1 : Real) <= d') :
    mu.real (E.horizontalCrossingEvent a b c d) <=
      mu.real (E.horizontalCrossingEvent
        (a + (z 0 : Real)) (b + (z 0 : Real)) c' d') := by
  rw [<- E.horizontalCrossing_translate_measureReal_eq mu hTI z a b c d]
  exact measureReal_mono
    (E.horizontalCrossingEvent_mono_vertical hc hd)



theorem one_sub_nat_mul_one_sub_le_pow (x : Real) (n : Nat)
    (hx0 : 0 <= x) (hx1 : x <= 1) :
    1 - (n : Real) * (1 - x) <= x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow0 : 0 <= x ^ n := pow_nonneg hx0 n
      have hpow1 : x ^ n <= 1 := pow_le_one₀ hx0 hx1
      calc
        1 - ((n + 1 : Nat) : Real) * (1 - x) =
            (1 - (n : Real) * (1 - x)) - (1 - x) := by
              push_cast
              ring
        _ <= x ^ n - (1 - x) := sub_le_sub_right ih _
        _ <= x ^ n * x := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hx1)
            (sub_nonneg.mpr hpow1)]
        _ = x ^ (n + 1) := by rw [pow_succ]



def finiteEventIntersection {Omega : Type*} :
    List (Set Omega) -> Set Omega
  | [] => Set.univ
  | A :: events => A ∩ finiteEventIntersection events

theorem finiteEventIntersection_measurable {Omega : Type*}
    [MeasurableSpace Omega] (events : List (Set Omega))
    (hmeasurable : forall A, A ∈ events -> MeasurableSet A) :
    MeasurableSet (finiteEventIntersection events) := by
  induction events with
  | nil => simp [finiteEventIntersection]
  | cons A events ih =>
      rw [finiteEventIntersection]
      exact (hmeasurable A (by simp)).inter
        (ih (fun B hB => hmeasurable B (by simp [hB])))

theorem finiteEventIntersection_isIncreasing
    {E : Type*} (events : List (Set (ConfigSpace E)))
    (hincreasing : forall A, A ∈ events -> IsIncreasing A) :
    IsIncreasing (finiteEventIntersection events) := by
  induction events with
  | nil =>
      intro omega eta _homega _heta
      exact Set.mem_univ eta
  | cons A events ih =>
      rw [finiteEventIntersection]
      exact (hincreasing A (by simp)).inter
        (ih (fun B hB => hincreasing B (by simp [hB])))




theorem finiteEventIntersection_append {Omega : Type*}
    (first second : List (Set Omega)) :
    finiteEventIntersection (first ++ second) =
      finiteEventIntersection first ∩ finiteEventIntersection second := by
  induction first with
  | nil => simp [finiteEventIntersection]
  | cons A first ih =>
      simp only [List.cons_append, finiteEventIntersection, ih]
      exact (Set.inter_assoc _ _ _).symm





theorem finiteEventIntersection_iterated_gluing {Omega : Type*}
    (target : Nat -> Set Omega) (stepEvents : Nat -> List (Set Omega))
    (n : Nat)
    (hstep : forall k, k < n ->
      finiteEventIntersection (target k :: stepEvents k) <= target (k + 1)) :
    finiteEventIntersection
        (target 0 :: (List.range n).flatMap stepEvents) <= target n := by
  induction n with
  | zero =>
      simpa [finiteEventIntersection]
  | succ n ih =>
      have hprevious : finiteEventIntersection
          (target 0 :: (List.range n).flatMap stepEvents) <= target n :=
        ih (fun k hk => hstep k (by omega))
      intro omega homega
      have hsplit : omega ∈
          finiteEventIntersection
              (target 0 :: (List.range n).flatMap stepEvents) ∩
            finiteEventIntersection (stepEvents n) := by
        rw [<- finiteEventIntersection_append]
        simpa only [List.range_succ, List.flatMap_append,
          List.flatMap_singleton, List.cons_append] using homega
      apply hstep n (by omega)
      exact ⟨hprevious hsplit.1, hsplit.2⟩




theorem PeriodicPlaneEmbedding.finiteEventIntersection_overlapCrossings
    (E : PeriodicPlaneEmbedding P) {B a l m b c d : ℝ}
    (hBpos : 0 < B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    (hal : a ≤ l) (hmb : m ≤ b)
    (hleft : a + 5 * B < m - 5 * B)
    (hright : l + 5 * B < b - 5 * B)
    (hheight : c + 5 * B < d - 5 * B) :
    finiteEventIntersection
      [E.horizontalCrossingEvent a m (c + 4 * B) (d - 4 * B),
       E.horizontalCrossingEvent l b (c + 4 * B) (d - 4 * B),
       E.verticalCrossingEvent (l + 4 * B) (m - 4 * B) c d] ⊆
      E.horizontalCrossingEvent a b c d := by
  simpa [finiteEventIntersection] using
    E.overlapCrossings_glue_horizontal hBpos hB hal hmb
      hleft hright hheight





theorem PeriodicPlaneEmbedding.iterated_overlapCrossings_glue_horizontal
    (E : PeriodicPlaneEmbedding P) (B a c d : Real)
    (left right : Nat -> Real) (n : Nat)
    (hBpos : 0 < B)
    (hB : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| <= B)
    (hal : forall k, k < n -> a <= left k)
    (hmb : forall k, k < n -> right k <= right (k + 1))
    (hleft : forall k, k < n -> a + 5 * B < right k - 5 * B)
    (hright : forall k, k < n ->
      left k + 5 * B < right (k + 1) - 5 * B)
    (hheight : forall k, k < n ->
      c - 4 * B * ((k + 1 : Nat) : Real) + 5 * B <
        d + 4 * B * ((k + 1 : Nat) : Real) - 5 * B) :
    let lower : Nat -> Real := fun k => c - 4 * B * (k : Real)
    let upper : Nat -> Real := fun k => d + 4 * B * (k : Real)
    let target : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
      E.horizontalCrossingEvent a (right k) (lower k) (upper k)
    let stepEvents : Nat -> List (Set (ConfigSpace (Sym2 V))) := fun k =>
      [E.horizontalCrossingEvent (left k) (right (k + 1))
          (lower k) (upper k),
       E.verticalCrossingEvent (left k + 4 * B) (right k - 4 * B)
          (lower (k + 1)) (upper (k + 1))]
    finiteEventIntersection
        (target 0 :: (List.range n).flatMap stepEvents) <= target n := by
  dsimp only
  let lower : Nat -> Real := fun k => c - 4 * B * (k : Real)
  let upper : Nat -> Real := fun k => d + 4 * B * (k : Real)
  let target : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    E.horizontalCrossingEvent a (right k) (lower k) (upper k)
  let stepEvents : Nat -> List (Set (ConfigSpace (Sym2 V))) := fun k =>
    [E.horizontalCrossingEvent (left k) (right (k + 1))
        (lower k) (upper k),
     E.verticalCrossingEvent (left k + 4 * B) (right k - 4 * B)
        (lower (k + 1)) (upper (k + 1))]
  apply finiteEventIntersection_iterated_gluing target stepEvents n
  intro k hk
  have hlower : lower (k + 1) + 4 * B = lower k := by
    dsimp only [lower]
    push_cast
    ring
  have hupper : upper (k + 1) - 4 * B = upper k := by
    dsimp only [upper]
    push_cast
    ring
  have hlocal := E.finiteEventIntersection_overlapCrossings
    hBpos hB (hal k hk) (hmb k hk) (hleft k hk) (hright k hk)
      (hheight k hk)
  change finiteEventIntersection
      [E.horizontalCrossingEvent a (right k) (lower k) (upper k),
       E.horizontalCrossingEvent (left k) (right (k + 1))
          (lower k) (upper k),
       E.verticalCrossingEvent (left k + 4 * B) (right k - 4 * B)
          (lower (k + 1)) (upper (k + 1))] <=
    E.horizontalCrossingEvent a (right (k + 1))
      (lower (k + 1)) (upper (k + 1))
  rw [<- hlower, <- hupper]
  exact hlocal



theorem finiteEventIntersection_measureReal_ge_pow
    {V : Type*} (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (s : Real) (hs : 0 <= s)
    (events : List (Set (ConfigSpace (Sym2 V))))
    (hmeasurable : forall A, A ∈ events -> MeasurableSet A)
    (hincreasing : forall A, A ∈ events -> IsIncreasing A)
    (hlower : forall A, A ∈ events -> s <= mu.real A) :
    s ^ events.length <= mu.real (finiteEventIntersection events) := by
  induction events with
  | nil => simp [finiteEventIntersection]
  | cons A events ih =>
      have hAm : MeasurableSet A := hmeasurable A (by simp)
      have hAi : IsIncreasing A := hincreasing A (by simp)
      have htailm : MeasurableSet (finiteEventIntersection events) :=
        finiteEventIntersection_measurable events
          (fun B hB => hmeasurable B (by simp [hB]))
      have htaili : IsIncreasing (finiteEventIntersection events) :=
        finiteEventIntersection_isIncreasing events
          (fun B hB => hincreasing B (by simp [hB]))
      have htail := ih
        (fun B hB => hmeasurable B (by simp [hB]))
        (fun B hB => hincreasing B (by simp [hB]))
        (fun B hB => hlower B (by simp [hB]))
      calc
        s ^ (A :: events).length = s ^ events.length * s := by
          simp only [List.length_cons, pow_succ]
        _ <= mu.real (finiteEventIntersection events) * mu.real A := by
          exact mul_le_mul htail (hlower A (by simp)) hs measureReal_nonneg
        _ = mu.real A * mu.real (finiteEventIntersection events) :=
          mul_comm _ _
        _ <= mu.real (A ∩ finiteEventIntersection events) :=
          hFKG A (finiteEventIntersection events) hAm htailm hAi htaili
        _ = mu.real (finiteEventIntersection (A :: events)) := rfl




theorem finiteEventIntersection_iterated_gluing_measureReal_ge_pow
    {V : Type*} (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (s : Real) (hs : 0 <= s)
    (target : Nat -> Set (ConfigSpace (Sym2 V)))
    (stepEvents : Nat -> List (Set (ConfigSpace (Sym2 V)))) (n : Nat)
    (hstep : forall k, k < n ->
      finiteEventIntersection (target k :: stepEvents k) <= target (k + 1))
    (hmeasurable : forall A,
      A ∈ target 0 :: (List.range n).flatMap stepEvents -> MeasurableSet A)
    (hincreasing : forall A,
      A ∈ target 0 :: (List.range n).flatMap stepEvents -> IsIncreasing A)
    (hlower : forall A,
      A ∈ target 0 :: (List.range n).flatMap stepEvents -> s <= mu.real A) :
    s ^ (target 0 :: (List.range n).flatMap stepEvents).length <=
      mu.real (target n) := by
  calc
    s ^ (target 0 :: (List.range n).flatMap stepEvents).length <=
        mu.real (finiteEventIntersection
          (target 0 :: (List.range n).flatMap stepEvents)) :=
      finiteEventIntersection_measureReal_ge_pow mu hFKG s hs _
        hmeasurable hincreasing hlower
    _ <= mu.real (target n) := measureReal_mono
      (finiteEventIntersection_iterated_gluing target stepEvents n hstep)





theorem PeriodicPlaneEmbedding.overlapCrossings_measureReal_ge_cube
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) {B a l m b c d s : ℝ}
    (hs : 0 ≤ s)
    (hBpos : 0 < B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    (hal : a ≤ l) (hmb : m ≤ b)
    (hleft : a + 5 * B < m - 5 * B)
    (hright : l + 5 * B < b - 5 * B)
    (hheight : c + 5 * B < d - 5 * B)
    (hfirst : s ≤ mu.real
      (E.horizontalCrossingEvent a m (c + 4 * B) (d - 4 * B)))
    (hsecond : s ≤ mu.real
      (E.horizontalCrossingEvent l b (c + 4 * B) (d - 4 * B)))
    (hconnector : s ≤ mu.real
      (E.verticalCrossingEvent (l + 4 * B) (m - 4 * B) c d)) :
    s ^ 3 ≤ mu.real (E.horizontalCrossingEvent a b c d) := by
  let events : List (Set (ConfigSpace (Sym2 V))) :=
    [E.horizontalCrossingEvent a m (c + 4 * B) (d - 4 * B),
     E.horizontalCrossingEvent l b (c + 4 * B) (d - 4 * B),
     E.verticalCrossingEvent (l + 4 * B) (m - 4 * B) c d]
  have hintersection : s ^ events.length ≤
      mu.real (finiteEventIntersection events) :=
    finiteEventIntersection_measureReal_ge_pow mu hFKG s hs events
      (by
        intro A hA
        simp only [events, List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl | rfl
        · exact E.horizontalCrossingEvent_measurableSet _ _ _ _
        · exact E.horizontalCrossingEvent_measurableSet _ _ _ _
        · exact E.verticalCrossingEvent_measurableSet _ _ _ _)
      (by
        intro A hA
        simp only [events, List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl | rfl
        · exact E.horizontalCrossingEvent_isIncreasing _ _ _ _
        · exact E.horizontalCrossingEvent_isIncreasing _ _ _ _
        · exact E.verticalCrossingEvent_isIncreasing _ _ _ _)
      (by
        intro A hA
        simp only [events, List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl | rfl
        · exact hfirst
        · exact hsecond
        · exact hconnector)
  calc
    s ^ 3 = s ^ events.length := by simp [events]
    _ ≤ mu.real (finiteEventIntersection events) := hintersection
    _ ≤ mu.real (E.horizontalCrossingEvent a b c d) :=
      measureReal_mono (by
        simpa only [events] using
          E.finiteEventIntersection_overlapCrossings hBpos hB hal hmb
            hleft hright hheight)




theorem PeriodicPlaneEmbedding.iterated_overlapCrossings_measureReal_ge_pow
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (B a c d : Real)
    (left right : Nat -> Real) (n : Nat) (s : Real) (hs : 0 <= s)
    (hBpos : 0 < B)
    (hB : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| <= B)
    (hal : forall k, k < n -> a <= left k)
    (hmb : forall k, k < n -> right k <= right (k + 1))
    (hleft : forall k, k < n -> a + 5 * B < right k - 5 * B)
    (hright : forall k, k < n ->
      left k + 5 * B < right (k + 1) - 5 * B)
    (hheight : forall k, k < n ->
      c - 4 * B * ((k + 1 : Nat) : Real) + 5 * B <
        d + 4 * B * ((k + 1 : Nat) : Real) - 5 * B)
    (hinitial : s <= mu.real
      (E.horizontalCrossingEvent a (right 0) c d))
    (hhorizontal : forall k, k < n -> s <= mu.real
      (E.horizontalCrossingEvent (left k) (right (k + 1))
        (c - 4 * B * (k : Real)) (d + 4 * B * (k : Real))))
    (hvertical : forall k, k < n -> s <= mu.real
      (E.verticalCrossingEvent (left k + 4 * B) (right k - 4 * B)
        (c - 4 * B * ((k + 1 : Nat) : Real))
        (d + 4 * B * ((k + 1 : Nat) : Real)))) :
    s ^ (1 + 2 * n) <= mu.real
      (E.horizontalCrossingEvent a (right n)
        (c - 4 * B * (n : Real)) (d + 4 * B * (n : Real))) := by
  let lower : Nat -> Real := fun k => c - 4 * B * (k : Real)
  let upper : Nat -> Real := fun k => d + 4 * B * (k : Real)
  let target : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    E.horizontalCrossingEvent a (right k) (lower k) (upper k)
  let stepEvents : Nat -> List (Set (ConfigSpace (Sym2 V))) := fun k =>
    [E.horizontalCrossingEvent (left k) (right (k + 1))
        (lower k) (upper k),
     E.verticalCrossingEvent (left k + 4 * B) (right k - 4 * B)
        (lower (k + 1)) (upper (k + 1))]
  let events := target 0 :: (List.range n).flatMap stepEvents
  have hdeterministic : finiteEventIntersection events <= target n := by
    simpa only [events, target, stepEvents, lower, upper] using
      E.iterated_overlapCrossings_glue_horizontal B a c d left right n
        hBpos hB hal hmb hleft hright hheight
  have hmeasurable : forall A, A ∈ events -> MeasurableSet A := by
    intro A hA
    simp only [events, List.mem_cons, List.mem_flatMap, List.mem_range] at hA
    rcases hA with rfl | ⟨k, hk, hA⟩
    · exact E.horizontalCrossingEvent_measurableSet _ _ _ _
    · simp only [stepEvents, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact E.horizontalCrossingEvent_measurableSet _ _ _ _
      · exact E.verticalCrossingEvent_measurableSet _ _ _ _
  have hincreasing : forall A, A ∈ events -> IsIncreasing A := by
    intro A hA
    simp only [events, List.mem_cons, List.mem_flatMap, List.mem_range] at hA
    rcases hA with rfl | ⟨k, hk, hA⟩
    · exact E.horizontalCrossingEvent_isIncreasing _ _ _ _
    · simp only [stepEvents, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact E.horizontalCrossingEvent_isIncreasing _ _ _ _
      · exact E.verticalCrossingEvent_isIncreasing _ _ _ _
  have hlower : forall A, A ∈ events -> s <= mu.real A := by
    intro A hA
    simp only [events, List.mem_cons, List.mem_flatMap, List.mem_range] at hA
    rcases hA with rfl | ⟨k, hk, hA⟩
    · simpa only [target, lower, upper, Nat.cast_zero, mul_zero,
        sub_zero, add_zero] using hinitial
    · simp only [stepEvents, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · simpa only [lower, upper] using hhorizontal k hk
      · simpa only [lower, upper] using hvertical k hk
  have hintersection : s ^ events.length <=
      mu.real (finiteEventIntersection events) :=
    finiteEventIntersection_measureReal_ge_pow mu hFKG s hs events
      hmeasurable hincreasing hlower
  have hlength : events.length = 1 + 2 * n := by
    simp only [events, List.length_cons, List.length_flatMap, stepEvents,
      List.length_cons]
    simp
    omega
  calc
    s ^ (1 + 2 * n) = s ^ events.length := by rw [hlength]
    _ <= mu.real (finiteEventIntersection events) := hintersection
    _ <= mu.real (target n) := measureReal_mono hdeterministic
    _ = mu.real (E.horizontalCrossingEvent a (right n)
        (c - 4 * B * (n : Real)) (d + 4 * B * (n : Real))) := rfl





structure PeriodicPlanarDualPair.CrossNestedOutwardPowerAspectComparison
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  exponent : Nat -> Nat
  horizontalEnd_ge_verticalStart_pow :
    forall (preparation : D.CrossNestedOutwardArrayPreparation mu) n,
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        ((preparation.array.chain n).level 0).raw.data.wideLeft
        ((preparation.array.chain n).level 0).raw.data.wideRight 0
        ((preparation.array.chain n).extentY 0))) ^ exponent n <=
      mu.real (D.primalEmbedding.horizontalCrossingEvent 0
        ((preparation.array.chain n).extentX (2 * (n + 1) + 2)) 0
        ((preparation.array.chain n).extentY (2 * (n + 1) + 2)))





structure PeriodicPlanarDualPair.CrossNestedOutwardAspectGluing
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  exponent : Nat -> Nat
  events : D.CrossNestedOutwardArrayPreparation mu -> Nat ->
    List (Set (ConfigSpace (Sym2 V)))
  length_events : forall preparation n,
    (events preparation n).length = exponent n
  measurable : forall preparation n A,
    A ∈ events preparation n -> MeasurableSet A
  increasing : forall preparation n A,
    A ∈ events preparation n -> IsIncreasing A
  source_le : forall preparation n A, A ∈ events preparation n ->
    mu.real (D.primalEmbedding.verticalCrossingEvent
      ((preparation.array.chain n).level 0).raw.data.wideLeft
      ((preparation.array.chain n).level 0).raw.data.wideRight 0
      ((preparation.array.chain n).extentY 0)) <= mu.real A
  glues : forall preparation n,
    finiteEventIntersection (events preparation n) <=
      D.primalEmbedding.horizontalCrossingEvent 0
        ((preparation.array.chain n).extentX (2 * (n + 1) + 2)) 0
        ((preparation.array.chain n).extentY (2 * (n + 1) + 2))



noncomputable def PeriodicPlanarDualPair.CrossNestedOutwardAspectGluing.toPowerComparison
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (gluing : D.CrossNestedOutwardAspectGluing mu) :
    D.CrossNestedOutwardPowerAspectComparison mu := by
  refine {
    exponent := gluing.exponent
    horizontalEnd_ge_verticalStart_pow := ?_ }
  intro preparation n
  let source := mu.real (D.primalEmbedding.verticalCrossingEvent
    ((preparation.array.chain n).level 0).raw.data.wideLeft
    ((preparation.array.chain n).level 0).raw.data.wideRight 0
    ((preparation.array.chain n).extentY 0))
  calc
    source ^ gluing.exponent n =
        source ^ (gluing.events preparation n).length := by
      rw [gluing.length_events preparation n]
    _ <= mu.real (finiteEventIntersection (gluing.events preparation n)) :=
      finiteEventIntersection_measureReal_ge_pow mu hFKG source
        measureReal_nonneg (gluing.events preparation n)
        (gluing.measurable preparation n)
        (gluing.increasing preparation n)
        (gluing.source_le preparation n)
    _ <= mu.real (D.primalEmbedding.horizontalCrossingEvent 0
        ((preparation.array.chain n).extentX (2 * (n + 1) + 2)) 0
        ((preparation.array.chain n).extentY (2 * (n + 1) + 2))) :=
      measureReal_mono (gluing.glues preparation n)




theorem PeriodicPlanarDualPair.CrossNestedOutwardPowerAspectComparison.nonempty_endpointCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (comparison : D.CrossNestedOutwardPowerAspectComparison mu)
    (preparation : D.CrossNestedOutwardArrayPreparation mu)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu)) :
    Nonempty (D.CrossNestedOutwardEndpointCertificate mu) := by
  let epsilon : Nat -> Real := fun n =>
    1 / ((n + 1 : Real) * (comparison.exponent n + 1 : Nat))
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  have hepsilon_le (n : Nat) : epsilon n <= 1 / (n + 1 : Real) := by
    dsimp only [epsilon]
    have hn : 0 < (n + 1 : Real) := by positivity
    have hm : 1 <= ((comparison.exponent n + 1 : Nat) : Real) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (comparison.exponent n))
    apply one_div_le_one_div_of_le hn
    nlinarith
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    apply squeeze_zero (fun n => (hepsilon n).le) hepsilon_le
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  obtain ⟨rebuilt, hverticalLower, hvertical⟩ :=
    preparation.exists_verticalEndpoint_rebuild_at_error D mu
      hFKG hTI hunique hTIDual epsilon hepsilon hepsilonZero
  let vertical : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      ((rebuilt.array.chain n).level 0).raw.data.wideLeft
      ((rebuilt.array.chain n).level 0).raw.data.wideRight 0
      ((rebuilt.array.chain n).extentY 0))
  let horizontal : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent 0
      ((rebuilt.array.chain n).extentX (2 * (n + 1) + 2)) 0
      ((rebuilt.array.chain n).extentY (2 * (n + 1) + 2)))
  have hweightedError (n : Nat) :
      (comparison.exponent n : Real) * epsilon n <=
        1 / (n + 1 : Real) := by
    dsimp only [epsilon]
    have hn : 0 < (n + 1 : Real) := by positivity
    have hm : 0 < ((comparison.exponent n + 1 : Nat) : Real) := by
      positivity
    have hfactor : (comparison.exponent n : Real) /
        (comparison.exponent n + 1 : Nat) <= 1 := by
      apply (div_le_one hm).2
      push_cast
      linarith
    calc
      (comparison.exponent n : Real) *
          (1 / ((n + 1 : Real) *
            (comparison.exponent n + 1 : Nat))) =
        ((comparison.exponent n : Real) /
            (comparison.exponent n + 1 : Nat)) *
            (1 / (n + 1 : Real)) := by
              field_simp
      _ <= 1 * (1 / (n + 1 : Real)) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = 1 / (n + 1 : Real) := one_mul _
  have hweightedErrorZero : Tendsto
      (fun n => (comparison.exponent n : Real) * epsilon n)
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact mul_nonneg (Nat.cast_nonneg _) (hepsilon n).le
    · exact hweightedError
    · simpa using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hlower : Tendsto (fun n =>
      1 - (comparison.exponent n : Real) * epsilon n)
      atTop (nhds 1) := by
    simpa using
      (tendsto_const_nhds (x := (1 : Real))).sub hweightedErrorZero
  have hhorizontal : Tendsto horizontal atTop (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower tendsto_const_nhds
    · intro n
      have hv0 : 0 <= vertical n := measureReal_nonneg
      have hv1 : vertical n <= 1 := measureReal_le_one
      have heps1 : epsilon n <= 1 :=
        (hepsilon_le n).trans (by
          have hn : (1 : Real) <= n + 1 := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          simpa using one_div_le_one_div_of_le (by norm_num) hn)
      have hbase0 : 0 <= 1 - epsilon n := sub_nonneg.mpr heps1
      have hbaseV : 1 - epsilon n <= vertical n :=
        le_of_lt (by simpa only [vertical] using hverticalLower n)
      calc
        1 - (comparison.exponent n : Real) * epsilon n =
            1 - (comparison.exponent n : Real) *
              (1 - (1 - epsilon n)) := by ring
        _ <= (1 - epsilon n) ^ comparison.exponent n :=
          one_sub_nat_mul_one_sub_le_pow (1 - epsilon n)
            (comparison.exponent n) hbase0 (by linarith)
        _ <= (vertical n) ^ comparison.exponent n := by
          exact pow_le_pow_left₀ hbase0 hbaseV _
        _ <= horizontal n := by
          simpa only [vertical, horizontal] using
            comparison.horizontalEnd_ge_verticalStart_pow rebuilt n
    · intro n
      exact measureReal_le_one
  exact ⟨{
    preparation := rebuilt
    verticalStart := by simpa only [vertical] using hvertical
    horizontalEnd := by simpa only [horizontal] using hhorizontal }⟩




theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_powerAspectComparison
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hcomparison :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        D.CrossNestedOutwardPowerAspectComparison mu) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only
  intro hcommon
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  have hmodel := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  obtain ⟨preparation⟩ :=
    D.exists_canonicalCrossNestedOutwardArrayPreparation_of_common
      hp hp1 hq hcommon
  have comparison : D.CrossNestedOutwardPowerAspectComparison mu :=
    hcomparison hcommon
  obtain ⟨certificate⟩ := comparison.nonempty_endpointCertificate
    D mu preparation hmodel.1 hmodel.2.1 hmodel.2.2.2.2.1
      hmodel.2.2.2.1
  exact certificate.false D mu hmodel.1 hmodel.2.1
    hmodel.2.2.2.2.1 hmodel.2.2.2.1



theorem PeriodicPlanarDualPair.strictDualNoCoexistence_of_powerAspectComparison_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 <= q)
    (hcomparison : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        D.CrossNestedOutwardPowerAspectComparison mu)
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    StrictDualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q := by
  apply D.strictDualNoCoexistence_of_sheffieldNotFull_logisticCylinders
    hconn hconnDual hq
  · intro p hp hp1
    exact D.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_powerAspectComparison
      hp hp1 hq (hcomparison p hp hp1)
  · exact hagrees




theorem PeriodicPlanarDualPair.dualCritical_relation_of_bidirectionalDecay_powerAspectComparison_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D)
    (Hdual : PolynomialConnectionShells D.swap)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 <= q)
    (hdecay : SubcriticalTwoPointExponentialDecay
      P q (P.criticalPoint q))
    (hdecayDual : SubcriticalTwoPointExponentialDecay
      Pdual q (Pdual.criticalPoint q))
    (hcomparison : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        D.CrossNestedOutwardPowerAspectComparison mu)
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  apply D.dualCritical_relation_of_bidirectionalExponentialDecay_strictNoCoexistence
    H Hdual hq hdecay hdecayDual
  exact D.strictDualNoCoexistence_of_powerAspectComparison_logisticCylinders
    hconn hconnDual hq hcomparison hagrees




theorem PeriodicPlanarDualPair.dualCritical_relation_of_bidirectionalDecay_aspectGluing_logisticCylinders
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D)
    (Hdual : PolynomialConnectionShells D.swap)
    (hconn : P.graph.Connected) (hconnDual : Pdual.graph.Connected)
    {q : Real} (hq : 1 <= q)
    (hdecay : SubcriticalTwoPointExponentialDecay
      P q (P.criticalPoint q))
    (hdecayDual : SubcriticalTwoPointExponentialDecay
      Pdual q (Pdual.criticalPoint q))
    (hgluing : forall (p : Real) (hp : 0 < p) (hp1 : p < 1),
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 ->
        D.CrossNestedOutwardAspectGluing mu)
    (hagrees :
      P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  apply D.dualCritical_relation_of_bidirectionalDecay_powerAspectComparison_logisticCylinders
    H Hdual hconn hconnDual hq hdecay hdecayDual
  · intro p hp hp1
    dsimp only
    intro hcommon
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    have hmodel := D.freeBufferedInfiniteVolume_sheffieldData_of_common
      hp hp1 hq hcommon
    exact (hgluing p hp hp1 hcommon).toPowerComparison D mu hmodel.1
  · exact hagrees

end StatMech.FK.PeriodicPlanar
