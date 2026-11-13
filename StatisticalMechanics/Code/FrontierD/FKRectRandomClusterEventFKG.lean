/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCutPushforward



namespace StatMech.FrontierD

noncomputable section


theorem fkRectCriticalEventMass_eq_indicatorExpectation
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) :
    fkRectCriticalEventMass R q A =
      ∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          A.indicator (fun _ => (1 : Real)) omega := by
  classical
  unfold fkRectCriticalEventMass
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hA : omega ∈ A <;> simp [Set.indicator, hA]

@[simp] theorem fkRectCriticalEventMass_univ
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    fkRectCriticalEventMass R q Set.univ = 1 := by
  unfold fkRectCriticalEventMass
  simp [sum_fkRectCriticalRandomClusterProb R hq]


theorem fkRectCriticalEventMass_compl_add
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass R q Aᶜ + fkRectCriticalEventMass R q A = 1 := by
  classical
  unfold fkRectCriticalEventMass
  rw [← Finset.sum_add_distrib]
  calc
    ∑ omega : R.Configuration,
        (Aᶜ.indicator
            (fun omega => fkRectCriticalRandomClusterProb R q omega) omega +
          A.indicator
            (fun omega => fkRectCriticalRandomClusterProb R q omega) omega) =
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega := by
            apply Finset.sum_congr rfl
            intro omega homega
            by_cases hA : omega ∈ A <;> simp [Set.indicator, hA]
    _ = 1 := sum_fkRectCriticalRandomClusterProb R hq

theorem fkRectCriticalEventMass_compl
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass R q Aᶜ =
      1 - fkRectCriticalEventMass R q A := by
  linarith [fkRectCriticalEventMass_compl_add R hq A]



theorem fkRectCriticalEventMass_mul_le_inter
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    {A B : Set R.Configuration}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    fkRectCriticalEventMass R q A * fkRectCriticalEventMass R q B ≤
      fkRectCriticalEventMass R q (A ∩ B) := by
  rw [fkRectCriticalEventMass_eq_indicatorExpectation,
    fkRectCriticalEventMass_eq_indicatorExpectation,
    fkRectCriticalEventMass_eq_indicatorExpectation]
  have hAB : (A ∩ B).indicator (fun _ => (1 : Real)) =
      fun omega =>
        A.indicator (fun _ => (1 : Real)) omega *
          B.indicator (fun _ => (1 : Real)) omega := by
    funext omega
    by_cases ha : omega ∈ A <;> by_cases hb : omega ∈ B <;>
      simp [Set.indicator, ha, hb, Set.mem_inter_iff]
  rw [hAB]
  exact fkRectCritical_positivelyAssociated R hq
    hA.indicator_monotone hB.indicator_monotone


theorem fkRectCriticalEventMass_mul_le_inter_decreasing
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    {A B : Set R.Configuration}
    (hA : IsDecreasing A) (hB : IsDecreasing B) :
    fkRectCriticalEventMass R q A * fkRectCriticalEventMass R q B ≤
      fkRectCriticalEventMass R q (A ∩ B) := by
  let f : R.Configuration -> Real :=
    A.indicator (fun _ => (1 : Real))
  let g : R.Configuration -> Real :=
    B.indicator (fun _ => (1 : Real))
  have hfanti : Antitone f := by
    intro omega tau hot
    by_cases homega : omega ∈ A
    · by_cases htau : tau ∈ A <;> simp [f, homega, htau]
    · have htau : tau ∉ A := fun htau => homega (hA hot htau)
      simp [f, homega, htau]
  have hganti : Antitone g := by
    intro omega tau hot
    by_cases homega : omega ∈ B
    · by_cases htau : tau ∈ B <;> simp [g, homega, htau]
    · have htau : tau ∉ B := fun htau => homega (hB hot htau)
      simp [g, homega, htau]
  have hfmono : Monotone (fun omega => -f omega) := fun _ _ h =>
    neg_le_neg (hfanti h)
  have hgmono : Monotone (fun omega => -g omega) := fun _ _ h =>
    neg_le_neg (hganti h)
  rw [fkRectCriticalEventMass_eq_indicatorExpectation,
    fkRectCriticalEventMass_eq_indicatorExpectation,
    fkRectCriticalEventMass_eq_indicatorExpectation]
  have hAB : (A ∩ B).indicator (fun _ => (1 : Real)) =
      fun omega => f omega * g omega := by
    funext omega
    by_cases ha : omega ∈ A <;> by_cases hb : omega ∈ B <;>
      simp [f, g, Set.indicator, ha, hb, Set.mem_inter_iff]
  rw [hAB]
  simpa only [mul_neg, Finset.sum_neg_distrib, neg_mul, neg_neg] using
    (fkRectCritical_positivelyAssociated R hq hfmono hgmono)



def fkRectFiniteEventIntersection {R : FKRectTorus} {ι : Type*}
    (s : Finset ι) (A : ι → Set R.Configuration) : Set R.Configuration :=
  {omega | ∀ i ∈ s, omega ∈ A i}

theorem fkRectFiniteEventIntersection_isIncreasing
    {R : FKRectTorus} {ι : Type*} (s : Finset ι)
    (A : ι → Set R.Configuration) (hA : ∀ i ∈ s, IsIncreasing (A i)) :
    IsIncreasing (fkRectFiniteEventIntersection s A) := by
  intro omega tau hot hmem i hi
  exact hA i hi hot (hmem i hi)

theorem fkRectFiniteEventIntersection_isDecreasing
    {R : FKRectTorus} {ι : Type*} (s : Finset ι)
    (A : ι → Set R.Configuration) (hA : ∀ i ∈ s, IsDecreasing (A i)) :
    IsDecreasing (fkRectFiniteEventIntersection s A) := by
  intro omega tau hot hmem i hi
  exact hA i hi hot (hmem i hi)



theorem fkRectCriticalEventMass_prod_le_finiteIntersection
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    {ι : Type*} (s : Finset ι) (A : ι → Set R.Configuration)
    (hA : ∀ i ∈ s, IsIncreasing (A i)) :
    (∏ i ∈ s, fkRectCriticalEventMass R q (A i)) ≤
      fkRectCriticalEventMass R q (fkRectFiniteEventIntersection s A) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [fkRectFiniteEventIntersection,
        fkRectCriticalEventMass_univ R (lt_of_lt_of_le zero_lt_one hq)]
  | @insert i s hi ih =>
      have hAi : IsIncreasing (A i) := hA i (Finset.mem_insert_self i s)
      have hAs : ∀ j ∈ s, IsIncreasing (A j) := by
        intro j hj
        exact hA j (Finset.mem_insert_of_mem hj)
      have hnonneg : 0 ≤ fkRectCriticalEventMass R q (A i) :=
        fkRectCriticalEventMass_nonneg R (lt_of_lt_of_le zero_lt_one hq) _
      calc
        (∏ j ∈ insert i s, fkRectCriticalEventMass R q (A j)) =
            fkRectCriticalEventMass R q (A i) *
              ∏ j ∈ s, fkRectCriticalEventMass R q (A j) := by
          rw [Finset.prod_insert hi]
        _ ≤ fkRectCriticalEventMass R q (A i) *
              fkRectCriticalEventMass R q
                (fkRectFiniteEventIntersection s A) :=
          mul_le_mul_of_nonneg_left (ih hAs) hnonneg
        _ ≤ fkRectCriticalEventMass R q
              (A i ∩ fkRectFiniteEventIntersection s A) :=
          fkRectCriticalEventMass_mul_le_inter R hq hAi
            (fkRectFiniteEventIntersection_isIncreasing s A hAs)
        _ = fkRectCriticalEventMass R q
              (fkRectFiniteEventIntersection (insert i s) A) := by
          congr 1
          ext omega
          simp [fkRectFiniteEventIntersection]


theorem fkRectCriticalEventMass_prod_le_finiteIntersection_decreasing
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    {ι : Type*} (s : Finset ι) (A : ι → Set R.Configuration)
    (hA : ∀ i ∈ s, IsDecreasing (A i)) :
    (∏ i ∈ s, fkRectCriticalEventMass R q (A i)) ≤
      fkRectCriticalEventMass R q (fkRectFiniteEventIntersection s A) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [fkRectFiniteEventIntersection,
        fkRectCriticalEventMass_univ R (lt_of_lt_of_le zero_lt_one hq)]
  | @insert i s hi ih =>
      have hAi : IsDecreasing (A i) := hA i (Finset.mem_insert_self i s)
      have hAs : ∀ j ∈ s, IsDecreasing (A j) := by
        intro j hj
        exact hA j (Finset.mem_insert_of_mem hj)
      have hnonneg : 0 ≤ fkRectCriticalEventMass R q (A i) :=
        fkRectCriticalEventMass_nonneg R (lt_of_lt_of_le zero_lt_one hq) _
      calc
        (∏ j ∈ insert i s, fkRectCriticalEventMass R q (A j)) =
            fkRectCriticalEventMass R q (A i) *
              ∏ j ∈ s, fkRectCriticalEventMass R q (A j) := by
          rw [Finset.prod_insert hi]
        _ ≤ fkRectCriticalEventMass R q (A i) *
              fkRectCriticalEventMass R q
                (fkRectFiniteEventIntersection s A) :=
          mul_le_mul_of_nonneg_left (ih hAs) hnonneg
        _ ≤ fkRectCriticalEventMass R q
              (A i ∩ fkRectFiniteEventIntersection s A) :=
          fkRectCriticalEventMass_mul_le_inter_decreasing R hq hAi
            (fkRectFiniteEventIntersection_isDecreasing s A hAs)
        _ = fkRectCriticalEventMass R q
              (fkRectFiniteEventIntersection (insert i s) A) := by
          congr 1
          ext omega
          simp [fkRectFiniteEventIntersection]



def fkRectTorusConnectionEvent (R : FKRectTorus)
    (x y : R.Vertex) : Set R.Configuration :=
  {omega | (fkRectOpenGraph R omega).Reachable x y}

theorem fkRectTorusConnectionEvent_isIncreasing
    (R : FKRectTorus) (x y : R.Vertex) :
    IsIncreasing (fkRectTorusConnectionEvent R x y) := by
  intro omega tau hot hreach
  exact hreach.mono (fkRectOpenGraph_mono R hot)


def fkRectTorusConnectionChainEvent (R : FKRectTorus)
    (s : Finset (R.Vertex × R.Vertex)) : Set R.Configuration :=
  fkRectFiniteEventIntersection s fun p =>
    fkRectTorusConnectionEvent R p.1 p.2

theorem fkRectTorusConnectionChainEvent_isIncreasing
    (R : FKRectTorus) (s : Finset (R.Vertex × R.Vertex)) :
    IsIncreasing (fkRectTorusConnectionChainEvent R s) := by
  apply fkRectFiniteEventIntersection_isIncreasing
  intro p hp
  exact fkRectTorusConnectionEvent_isIncreasing R p.1 p.2


theorem fkRectCriticalEventMass_connectionChain_ge_prod
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (s : Finset (R.Vertex × R.Vertex)) :
    (∏ p ∈ s, fkRectCriticalEventMass R q
        (fkRectTorusConnectionEvent R p.1 p.2)) ≤
      fkRectCriticalEventMass R q
        (fkRectTorusConnectionChainEvent R s) := by
  exact fkRectCriticalEventMass_prod_le_finiteIntersection R hq s
    (fun p => fkRectTorusConnectionEvent R p.1 p.2)
    (fun p _ => fkRectTorusConnectionEvent_isIncreasing R p.1 p.2)



theorem fkRectCriticalEventMass_connectionChain_ge_pow
    (R : FKRectTorus) {q a : Real} (hq : 1 ≤ q) (ha : 0 ≤ a)
    (s : Finset (R.Vertex × R.Vertex))
    (hblock : ∀ p ∈ s, a ≤ fkRectCriticalEventMass R q
      (fkRectTorusConnectionEvent R p.1 p.2)) :
    a ^ s.card ≤ fkRectCriticalEventMass R q
      (fkRectTorusConnectionChainEvent R s) := by
  calc
    a ^ s.card = ∏ _p ∈ s, a := by simp
    _ ≤ ∏ p ∈ s, fkRectCriticalEventMass R q
        (fkRectTorusConnectionEvent R p.1 p.2) := by
      exact Finset.prod_le_prod (fun _ _ => ha) hblock
    _ ≤ fkRectCriticalEventMass R q
        (fkRectTorusConnectionChainEvent R s) :=
      fkRectCriticalEventMass_connectionChain_ge_prod R hq s



theorem fkRectCriticalEventMass_event_mul_connectionChain_le
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (B : Set R.Configuration) (hB : IsIncreasing B)
    (s : Finset (R.Vertex × R.Vertex)) :
    fkRectCriticalEventMass R q B *
        (∏ p ∈ s, fkRectCriticalEventMass R q
          (fkRectTorusConnectionEvent R p.1 p.2)) ≤
      fkRectCriticalEventMass R q
        (B ∩ fkRectTorusConnectionChainEvent R s) := by
  have hchain := fkRectCriticalEventMass_connectionChain_ge_prod R hq s
  have hBnonneg := fkRectCriticalEventMass_nonneg R
    (lt_of_lt_of_le zero_lt_one hq) B
  calc
    _ ≤ fkRectCriticalEventMass R q B *
        fkRectCriticalEventMass R q
          (fkRectTorusConnectionChainEvent R s) :=
      mul_le_mul_of_nonneg_left hchain hBnonneg
    _ ≤ _ := fkRectCriticalEventMass_mul_le_inter R hq hB
      (fkRectTorusConnectionChainEvent_isIncreasing R s)


theorem fkRectCriticalEventMass_event_mul_pow_le_connectionChain
    (R : FKRectTorus) {q a : Real} (hq : 1 ≤ q) (ha : 0 ≤ a)
    (B : Set R.Configuration) (hB : IsIncreasing B)
    (s : Finset (R.Vertex × R.Vertex))
    (hblock : ∀ p ∈ s, a ≤ fkRectCriticalEventMass R q
      (fkRectTorusConnectionEvent R p.1 p.2)) :
    fkRectCriticalEventMass R q B * a ^ s.card ≤
      fkRectCriticalEventMass R q
        (B ∩ fkRectTorusConnectionChainEvent R s) := by
  have hpow := fkRectCriticalEventMass_connectionChain_ge_pow
    R hq ha s hblock
  have hBnonneg := fkRectCriticalEventMass_nonneg R
    (lt_of_lt_of_le zero_lt_one hq) B
  calc
    _ ≤ fkRectCriticalEventMass R q B *
        fkRectCriticalEventMass R q
          (fkRectTorusConnectionChainEvent R s) :=
      mul_le_mul_of_nonneg_left hpow hBnonneg
    _ ≤ _ := fkRectCriticalEventMass_mul_le_inter R hq hB
      (fkRectTorusConnectionChainEvent_isIncreasing R s)


def fkRectFiniteEventUnion {R : FKRectTorus} {ι : Type*}
    (s : Finset ι) (A : ι → Set R.Configuration) : Set R.Configuration :=
  {omega | ∃ i ∈ s, omega ∈ A i}


theorem fkRectCriticalEventMass_finiteUnion_le_sum
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    {ι : Type*} (s : Finset ι) (A : ι → Set R.Configuration) :
    fkRectCriticalEventMass R q (fkRectFiniteEventUnion s A) ≤
      ∑ i ∈ s, fkRectCriticalEventMass R q (A i) := by
  classical
  unfold fkRectCriticalEventMass
  have hpoint (omega : R.Configuration) :
      (fkRectFiniteEventUnion s A).indicator
          (fun omega => fkRectCriticalRandomClusterProb R q omega) omega ≤
        ∑ i ∈ s, (A i).indicator
          (fun omega => fkRectCriticalRandomClusterProb R q omega) omega := by
    by_cases hU : omega ∈ fkRectFiniteEventUnion s A
    · have hU' := hU
      obtain ⟨i, hi, hAi⟩ := hU
      rw [Set.indicator_of_mem hU']
      have hle := Finset.single_le_sum
        (s := s)
        (f := fun j => (A j).indicator
          (fun eta => fkRectCriticalRandomClusterProb R q eta) omega)
        (fun j hj => Set.indicator_nonneg
          (fun _ _ => fkRectCriticalRandomClusterProb_nonneg R hq _) _)
        hi
      simpa [Set.indicator_of_mem hAi] using hle
    · rw [Set.indicator_of_notMem hU]
      exact Finset.sum_nonneg fun i _ => Set.indicator_nonneg
        (fun _ _ => fkRectCriticalRandomClusterProb_nonneg R hq _) _
  calc
    (∑ omega : R.Configuration,
      (fkRectFiniteEventUnion s A).indicator
        (fun omega => fkRectCriticalRandomClusterProb R q omega) omega) ≤
        ∑ omega : R.Configuration, ∑ i ∈ s,
          (A i).indicator
            (fun omega => fkRectCriticalRandomClusterProb R q omega) omega :=
      Finset.sum_le_sum fun omega _ => hpoint omega
    _ = ∑ i ∈ s, ∑ omega : R.Configuration,
          (A i).indicator
            (fun omega => fkRectCriticalRandomClusterProb R q omega) omega := by
      rw [Finset.sum_comm]


theorem fkRectCriticalEventMass_union_le_add
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A B : Set R.Configuration) :
    fkRectCriticalEventMass R q (A ∪ B) ≤
      fkRectCriticalEventMass R q A + fkRectCriticalEventMass R q B := by
  let E : Bool → Set R.Configuration := fun b => if b then A else B
  have hset : A ∪ B = fkRectFiniteEventUnion Finset.univ E := by
    ext omega
    constructor
    · rintro (hA | hB)
      · exact ⟨true, Finset.mem_univ _, by simpa [E] using hA⟩
      · exact ⟨false, Finset.mem_univ _, by simpa [E] using hB⟩
    · rintro ⟨b, _, hb⟩
      cases b
      · exact Or.inr (by simpa [E] using hb)
      · exact Or.inl (by simpa [E] using hb)
  rw [hset]
  have h := fkRectCriticalEventMass_finiteUnion_le_sum
    R hq Finset.univ E
  simpa [E, add_comm] using h




theorem exists_card_mul_eventMass_ge_of_finiteUnion_ge
    (R : FKRectTorus) {q c : Real} (hq : 0 < q)
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (A : ι → Set R.Configuration)
    (hc : c ≤ fkRectCriticalEventMass R q
      (fkRectFiniteEventUnion s A)) :
    ∃ i ∈ s, c ≤ (s.card : Real) * fkRectCriticalEventMass R q (A i) := by
  classical
  have hsum := hc.trans
    (fkRectCriticalEventMass_finiteUnion_le_sum R hq s A)
  by_contra hex
  have hex' : ∀ i ∈ s,
      (s.card : Real) * fkRectCriticalEventMass R q (A i) < c := by
    intro i hi
    exact lt_of_not_ge (fun h => hex ⟨i, hi, h⟩)
  have hcardPos : (0 : Real) < s.card := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hstrict :
      ∑ i ∈ s, (s.card : Real) * fkRectCriticalEventMass R q (A i) <
        ∑ i ∈ s, c :=
    Finset.sum_lt_sum_of_nonempty hs (fun i hi => hex' i hi)
  rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hstrict
  nlinarith

end

end StatMech.FrontierD
