/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib










namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def finiteReturnWitness (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) :
    exists n : Nat, 0 < n /\ selected ((sigma ^ n) x.1) := by
  refine ⟨orderOf sigma, orderOf_pos sigma, ?_⟩
  rw [pow_orderOf_eq_one]
  exact x.2

noncomputable def finiteFirstReturnTime
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) : Nat :=
  Nat.find (finiteReturnWitness sigma selected x)

theorem finiteFirstReturnTime_pos
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) :
    0 < finiteFirstReturnTime sigma selected x :=
  (Nat.find_spec (finiteReturnWitness sigma selected x)).1

theorem finiteFirstReturnTime_selected
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) :
    selected ((sigma ^ finiteFirstReturnTime sigma selected x) x.1) :=
  (Nat.find_spec (finiteReturnWitness sigma selected x)).2

theorem finiteFirstReturnTime_minimal
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a})
    (n : Nat) (hn : n < finiteFirstReturnTime sigma selected x) :
    Not (0 < n /\ selected ((sigma ^ n) x.1)) :=
  Nat.find_min (finiteReturnWitness sigma selected x) hn

noncomputable def finiteFirstReturn
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) :
    {a : A // selected a} :=
  ⟨(sigma ^ finiteFirstReturnTime sigma selected x) x.1,
    finiteFirstReturnTime_selected sigma selected x⟩

theorem finitePerm_pow_sub_apply_eq_of_pow_apply_eq
    (sigma : Equiv.Perm A) (x y : A) (m n : Nat)
    (hmn : m <= n)
    (h : (sigma ^ m) x = (sigma ^ n) y) :
    x = (sigma ^ (n - m)) y := by
  apply (sigma ^ m).injective
  rw [h]
  have hn : n = m + (n - m) := (Nat.add_sub_of_le hmn).symm
  nth_rewrite 1 [hn]
  rw [pow_add, Equiv.Perm.mul_apply]

theorem finiteFirstReturn_injective
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] :
    Function.Injective (finiteFirstReturn sigma selected) := by
  intro x y hxy
  apply Subtype.ext
  let m := finiteFirstReturnTime sigma selected x
  let n := finiteFirstReturnTime sigma selected y
  have hpowers : (sigma ^ m) x.1 = (sigma ^ n) y.1 :=
    congrArg Subtype.val hxy
  rcases le_total m n with hmn | hnm
  · have hback := finitePerm_pow_sub_apply_eq_of_pow_apply_eq
      sigma x.1 y.1 m n hmn hpowers
    by_cases hmnEq : m = n
    · apply (sigma ^ m).injective
      simpa [hmnEq] using hpowers
    · have hpos : 0 < n - m :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hmn hmnEq)
      have hlt : n - m < n := Nat.sub_lt
        (finiteFirstReturnTime_pos sigma selected y)
        (finiteFirstReturnTime_pos sigma selected x)
      exact False.elim ((finiteFirstReturnTime_minimal sigma selected y
        (n - m) hlt) ⟨hpos, hback ▸ x.2⟩)
  · have hback := finitePerm_pow_sub_apply_eq_of_pow_apply_eq
      sigma y.1 x.1 n m hnm hpowers.symm
    by_cases hnmEq : n = m
    · apply (sigma ^ m).injective
      simpa [hnmEq] using hpowers
    · have hpos : 0 < m - n :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hnm hnmEq)
      have hlt : m - n < m := Nat.sub_lt
        (finiteFirstReturnTime_pos sigma selected x)
        (finiteFirstReturnTime_pos sigma selected y)
      exact False.elim ((finiteFirstReturnTime_minimal sigma selected x
        (m - n) hlt) ⟨hpos, hback ▸ y.2⟩)

noncomputable def finiteFirstReturnPerm
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] : Equiv.Perm {a : A // selected a} :=
  Equiv.ofBijective (finiteFirstReturn sigma selected)
    ((Fintype.bijective_iff_injective_and_card
      (finiteFirstReturn sigma selected)).2
        ⟨finiteFirstReturn_injective sigma selected, rfl⟩)

@[simp] theorem finiteFirstReturnPerm_apply
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) :
    finiteFirstReturnPerm sigma selected x =
    finiteFirstReturn sigma selected x :=
  rfl



theorem finiteFirstReturnPerm_pow_eq_ambient_pow
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) (n : Nat) :
    exists k : Nat,
      ((finiteFirstReturnPerm sigma selected ^ n) x).1 =
        (sigma ^ k) x.1 := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      let y := (finiteFirstReturnPerm sigma selected ^ n) x
      let t := finiteFirstReturnTime sigma selected y
      refine ⟨t + k, ?_⟩
      rw [pow_succ', Equiv.Perm.mul_apply,
        finiteFirstReturnPerm_apply]
      change (sigma ^ t) y.1 = (sigma ^ (t + k)) x.1
      rw [hk, pow_add, Equiv.Perm.mul_apply]


theorem finiteFirstReturnPerm_sameCycle_ambient
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x y : {a : A // selected a})
    (hcycle : (finiteFirstReturnPerm sigma selected).SameCycle x y) :
    sigma.SameCycle x.1 y.1 := by
  obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
  obtain ⟨k, hk⟩ := finiteFirstReturnPerm_pow_eq_ambient_pow
    sigma selected x n
  rw [hn] at hk
  exact ⟨k, by simpa using hk.symm⟩



noncomputable def finiteFirstReturnSegment
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) : List A :=
  List.ofFn fun k : Fin (finiteFirstReturnTime sigma selected x) =>
    (sigma ^ k.val) x.1

@[simp] theorem length_finiteFirstReturnSegment
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) :
    (finiteFirstReturnSegment sigma selected x).length =
      finiteFirstReturnTime sigma selected x := by
  simp [finiteFirstReturnSegment]

theorem finiteFirstReturnSegment_nodup
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) :
    (finiteFirstReturnSegment sigma selected x).Nodup := by
  rw [finiteFirstReturnSegment, List.nodup_ofFn]
  intro i j hij
  apply Fin.ext
  rcases le_total i.val j.val with hle | hle
  · by_cases heq : i.val = j.val
    · exact heq
    · have hback : x.1 = (sigma ^ (j.val - i.val)) x.1 :=
        finitePerm_pow_sub_apply_eq_of_pow_apply_eq sigma
          x.1 x.1 i.val j.val hle hij
      have hpos : 0 < j.val - i.val :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hle heq)
      have hlt : j.val - i.val <
          finiteFirstReturnTime sigma selected x := by omega
      exact False.elim ((finiteFirstReturnTime_minimal sigma selected x
        (j.val - i.val) hlt) ⟨hpos, hback ▸ x.2⟩)
  · by_cases heq : j.val = i.val
    · exact heq.symm
    · have hback : x.1 = (sigma ^ (i.val - j.val)) x.1 :=
        finitePerm_pow_sub_apply_eq_of_pow_apply_eq sigma
          x.1 x.1 j.val i.val hle hij.symm
      have hpos : 0 < i.val - j.val :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hle heq)
      have hlt : i.val - j.val <
          finiteFirstReturnTime sigma selected x := by omega
      exact False.elim ((finiteFirstReturnTime_minimal sigma selected x
        (i.val - j.val) hlt) ⟨hpos, hback ▸ x.2⟩)

theorem finiteFirstReturnSegment_disjoint
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected]
    (x y : {a : A // selected a}) (hxy : x ≠ y) :
    (finiteFirstReturnSegment sigma selected x).Disjoint
      (finiteFirstReturnSegment sigma selected y) := by
  rw [List.disjoint_left]
  intro d hdx hdy
  rw [finiteFirstReturnSegment, List.mem_ofFn] at hdx hdy
  obtain ⟨i, hi⟩ := hdx
  obtain ⟨j, hj⟩ := hdy
  have hpowers : (sigma ^ i.val) x.1 = (sigma ^ j.val) y.1 :=
    hi.trans hj.symm
  rcases le_total i.val j.val with hle | hle
  · by_cases heq : i.val = j.val
    · apply hxy
      apply Subtype.ext
      apply (sigma ^ i.val).injective
      simpa [heq] using hpowers
    · have hback : x.1 = (sigma ^ (j.val - i.val)) y.1 :=
        finitePerm_pow_sub_apply_eq_of_pow_apply_eq sigma
          x.1 y.1 i.val j.val hle hpowers
      have hpos : 0 < j.val - i.val :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hle heq)
      have hlt : j.val - i.val <
          finiteFirstReturnTime sigma selected y := by omega
      exact (finiteFirstReturnTime_minimal sigma selected y
        (j.val - i.val) hlt) ⟨hpos, hback ▸ x.2⟩
  · by_cases heq : j.val = i.val
    · apply hxy
      apply Subtype.ext
      apply (sigma ^ i.val).injective
      simpa [heq] using hpowers
    · have hback : y.1 = (sigma ^ (i.val - j.val)) x.1 :=
        finitePerm_pow_sub_apply_eq_of_pow_apply_eq sigma
          y.1 x.1 j.val i.val hle hpowers.symm
      have hpos : 0 < i.val - j.val :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hle heq)
      have hlt : i.val - j.val <
          finiteFirstReturnTime sigma selected x := by omega
      exact (finiteFirstReturnTime_minimal sigma selected x
        (i.val - j.val) hlt) ⟨hpos, hback ▸ y.2⟩

noncomputable def finiteFirstReturnSegments
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a}) : List A :=
  states.flatMap (finiteFirstReturnSegment sigma selected)

theorem mem_finiteFirstReturnSegments_iff
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (d : A) :
    d ∈ finiteFirstReturnSegments sigma selected states ↔
      ∃ x ∈ states, ∃ k : Nat,
        k < finiteFirstReturnTime sigma selected x ∧
          (sigma ^ k) x.1 = d := by
  simp only [finiteFirstReturnSegments, List.mem_flatMap,
    finiteFirstReturnSegment, List.mem_ofFn]
  constructor
  · rintro ⟨x, hx, k, hk⟩
    exact ⟨x, hx, k.val, k.isLt, hk⟩
  · rintro ⟨x, hx, k, hk, hd⟩
    exact ⟨x, hx, ⟨⟨k, hk⟩, hd⟩⟩



theorem mem_finiteFirstReturnSegments_step_iff_of_not_selected
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (d : A) (hnext : Not (selected (sigma d))) :
    sigma d ∈ finiteFirstReturnSegments sigma selected states ↔
      d ∈ finiteFirstReturnSegments sigma selected states := by
  rw [mem_finiteFirstReturnSegments_iff,
    mem_finiteFirstReturnSegments_iff]
  constructor
  · rintro ⟨x, hx, k, hk, hpow⟩
    have hkpos : 0 < k := by
      by_contra hnot
      have hkzero : k = 0 := by omega
      subst k
      apply hnext
      rw [← hpow]
      exact x.2
    refine ⟨x, hx, k - 1, by omega, ?_⟩
    apply sigma.injective
    calc
      sigma ((sigma ^ (k - 1)) x.1) =
          (sigma ^ k) x.1 := by
        rw [show k = (k - 1) + 1 by omega, pow_succ']
        rfl
      _ = sigma d := hpow
  · rintro ⟨x, hx, k, hk, hpow⟩
    have hsucc : k + 1 < finiteFirstReturnTime sigma selected x := by
      by_contra hnot
      have heq : k + 1 = finiteFirstReturnTime sigma selected x := by omega
      apply hnext
      rw [← hpow]
      rw [show sigma ((sigma ^ k) x.1) =
          (sigma ^ (k + 1)) x.1 by rw [pow_succ']; rfl, heq]
      exact finiteFirstReturnTime_selected sigma selected x
    refine ⟨x, hx, k + 1, hsucc, ?_⟩
    rw [← hpow, pow_succ']
    rfl



theorem mem_finiteFirstReturnSegments_predecessor_iff
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (d : A) (y : {a : A // selected a}) (hstep : sigma d = y.1) :
    d ∈ finiteFirstReturnSegments sigma selected states ↔
      (finiteFirstReturnPerm sigma selected).symm y ∈ states := by
  rw [mem_finiteFirstReturnSegments_iff]
  constructor
  · rintro ⟨x, hx, k, hk, hpow⟩
    have hpowsucc : (sigma ^ (k + 1)) x.1 = y.1 := by
      rw [pow_succ']
      exact congrArg sigma hpow |>.trans hstep
    have hlast : k + 1 = finiteFirstReturnTime sigma selected x := by
      by_contra hne
      have hlt : k + 1 < finiteFirstReturnTime sigma selected x := by omega
      exact (finiteFirstReturnTime_minimal sigma selected x (k + 1) hlt)
        ⟨by omega, hpowsucc ▸ y.2⟩
    have hreturn : finiteFirstReturnPerm sigma selected x = y := by
      apply Subtype.ext
      change (sigma ^ finiteFirstReturnTime sigma selected x) x.1 = y.1
      rw [← hlast]
      exact hpowsucc
    have hxprev : x = (finiteFirstReturnPerm sigma selected).symm y := by
      apply (finiteFirstReturnPerm sigma selected).injective
      rw [hreturn, (finiteFirstReturnPerm sigma selected).apply_symm_apply]
    rwa [← hxprev]
  · intro hprev
    let x := (finiteFirstReturnPerm sigma selected).symm y
    let time := finiteFirstReturnTime sigma selected x
    have htime : 0 < time := finiteFirstReturnTime_pos sigma selected x
    have hreturn : finiteFirstReturnPerm sigma selected x = y := by
      simp [x]
    have hlast : (sigma ^ (time - 1)) x.1 = d := by
      apply sigma.injective
      calc
        sigma ((sigma ^ (time - 1)) x.1) =
            (sigma ^ time) x.1 := by
          rw [show time = (time - 1) + 1 by omega, pow_succ']
          rfl
        _ = y.1 := congrArg Subtype.val hreturn
        _ = sigma d := hstep.symm
    exact ⟨x, hprev, time - 1, by omega, hlast⟩

theorem finiteFirstReturnSegments_nodup
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (hstates : states.Nodup) :
    (finiteFirstReturnSegments sigma selected states).Nodup := by
  rw [finiteFirstReturnSegments, List.nodup_flatMap]
  constructor
  · intro x hx
    exact finiteFirstReturnSegment_nodup sigma selected x
  · exact (List.nodup_iff_pairwise_ne.mp hstates).imp (fun hxy =>
      finiteFirstReturnSegment_disjoint sigma selected _ _ hxy)

abbrev FiniteFirstReturnOccurrenceIndex
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a}) :=
  (i : Fin states.length) ×
    Fin (finiteFirstReturnTime sigma selected (states.get i))

noncomputable def finiteFirstReturnOccurrencePoint
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (x : FiniteFirstReturnOccurrenceIndex sigma selected states) : A :=
  (sigma ^ x.2.val) (states.get x.1).1

theorem finiteFirstReturnOccurrencePoint_injective
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (hstates : states.Nodup) :
    Function.Injective
      (finiteFirstReturnOccurrencePoint sigma selected states) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ hpoint
  have hstate : states.get i = states.get j := by
    by_contra hne
    have hdisjoint := finiteFirstReturnSegment_disjoint sigma selected
      (states.get i) (states.get j) hne
    rw [List.disjoint_left] at hdisjoint
    apply hdisjoint
      (List.mem_ofFn.mpr ⟨k, rfl⟩)
    apply List.mem_ofFn.mpr
    refine ⟨l, ?_⟩
    exact hpoint.symm
  have hij : i = j := hstates.injective_get hstate
  subst j
  have hkl : k = l := by
    apply (List.nodup_ofFn.mp
      (finiteFirstReturnSegment_nodup sigma selected (states.get i)))
    exact hpoint
  subst l
  rfl

def finiteFirstReturnOccurrenceIndexSucc
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (x : FiniteFirstReturnOccurrenceIndex sigma selected states)
    (hnext : x.2.val + 1 <
      finiteFirstReturnTime sigma selected (states.get x.1)) :
    FiniteFirstReturnOccurrenceIndex sigma selected states :=
  ⟨x.1, ⟨x.2.val + 1, hnext⟩⟩

theorem finiteFirstReturnOccurrencePoint_succ
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (x : FiniteFirstReturnOccurrenceIndex sigma selected states)
    (hnext : x.2.val + 1 <
      finiteFirstReturnTime sigma selected (states.get x.1)) :
    sigma (finiteFirstReturnOccurrencePoint sigma selected states x) =
      finiteFirstReturnOccurrencePoint sigma selected states
        (finiteFirstReturnOccurrenceIndexSucc
          sigma selected states x hnext) := by
  simp [finiteFirstReturnOccurrencePoint,
    finiteFirstReturnOccurrenceIndexSucc, pow_succ', Equiv.Perm.mul_apply]

theorem finiteFirstReturnOccurrencePoint_last
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (x : FiniteFirstReturnOccurrenceIndex sigma selected states)
    (hlast : x.2.val + 1 =
      finiteFirstReturnTime sigma selected (states.get x.1)) :
    sigma (finiteFirstReturnOccurrencePoint sigma selected states x) =
      (finiteFirstReturn sigma selected (states.get x.1)).1 := by
  change sigma ((sigma ^ x.2.val) (states.get x.1).1) =
    (sigma ^ finiteFirstReturnTime sigma selected (states.get x.1))
      (states.get x.1).1
  calc
    sigma ((sigma ^ x.2.val) (states.get x.1).1) =
        (sigma ^ (x.2.val + 1)) (states.get x.1).1 := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    _ = (sigma ^ finiteFirstReturnTime sigma selected (states.get x.1))
        (states.get x.1).1 := by rw [hlast]

theorem finiteFirstReturnOccurrencePoint_step_interior
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected]
    (states : List {a : A // selected a})
    (i : Fin states.length) (k : Nat)
    (hk : k + 1 < finiteFirstReturnTime sigma selected (states.get i)) :
    sigma (finiteFirstReturnOccurrencePoint sigma selected states
        ⟨i, ⟨k, by omega⟩⟩) =
      finiteFirstReturnOccurrencePoint sigma selected states
        ⟨i, ⟨k + 1, hk⟩⟩ := by
  simp only [finiteFirstReturnOccurrencePoint]
  rw [show k + 1 = Nat.succ k by omega, pow_succ']
  rfl

theorem finiteFirstReturnOccurrencePoint_step_endpoint
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected]
    (states : List {a : A // selected a})
    (i : Fin states.length) (k : Nat)
    (hk : k < finiteFirstReturnTime sigma selected (states.get i))
    (hlast : k + 1 =
      finiteFirstReturnTime sigma selected (states.get i)) :
    sigma (finiteFirstReturnOccurrencePoint sigma selected states
        ⟨i, ⟨k, hk⟩⟩) =
      (finiteFirstReturn sigma selected (states.get i)).1 := by
  simp only [finiteFirstReturnOccurrencePoint, finiteFirstReturn]
  rw [← hlast, show k + 1 = Nat.succ k by omega, pow_succ']
  rfl

def finiteFirstReturnOccurrenceIndexZero
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (i : Fin states.length) :
    FiniteFirstReturnOccurrenceIndex sigma selected states :=
  ⟨i, ⟨0, finiteFirstReturnTime_pos
    sigma selected (states.get i)⟩⟩

@[simp] theorem finiteFirstReturnOccurrencePoint_zero
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (i : Fin states.length) :
    finiteFirstReturnOccurrencePoint sigma selected states
        (finiteFirstReturnOccurrenceIndexZero sigma selected states i) =
      (states.get i).1 := by
  simp [finiteFirstReturnOccurrencePoint,
    finiteFirstReturnOccurrenceIndexZero]

section Related

variable {B : Type*} [Fintype B] [DecidableEq B]



theorem finiteRelated_until_firstReturn
    (sigma : Equiv.Perm A) (tau : Equiv.Perm B)
    (selectedA : A -> Prop) (selectedB : B -> Prop)
    [DecidablePred selectedA] [DecidablePred selectedB]
    (R : A -> B -> Prop)
    (hstep : forall {a b}, R a b -> Not (selectedA a) ->
      Not (selectedB b) -> R (sigma a) (tau b))
    (x : {a : A // selectedA a}) (y : {b : B // selectedB b})
    (hfirst : R (sigma x.1) (tau y.1))
    (n : Nat) (hnpos : 0 < n)
    (hnA : n <= finiteFirstReturnTime sigma selectedA x)
    (hnB : n <= finiteFirstReturnTime tau selectedB y) :
    R ((sigma ^ n) x.1) ((tau ^ n) y.1) := by
  induction n using Nat.case_strong_induction_on with
  | hz => exact False.elim (by omega)
  | hi n ih =>
      by_cases hnzero : n = 0
      · subst n
        simpa [Equiv.Perm.mul_apply] using hfirst
      · have hnpos' : 0 < n := Nat.pos_of_ne_zero hnzero
        have hnA' : n <= finiteFirstReturnTime sigma selectedA x := by omega
        have hnB' : n <= finiteFirstReturnTime tau selectedB y := by omega
        have hrel := ih n (by omega) hnpos' hnA' hnB'
        have hnAlt : n < finiteFirstReturnTime sigma selectedA x := by omega
        have hnBlt : n < finiteFirstReturnTime tau selectedB y := by omega
        have hnotA : Not (selectedA ((sigma ^ n) x.1)) := by
          intro hs
          exact (finiteFirstReturnTime_minimal sigma selectedA x n hnAlt)
            ⟨hnpos', hs⟩
        have hnotB : Not (selectedB ((tau ^ n) y.1)) := by
          intro hs
          exact (finiteFirstReturnTime_minimal tau selectedB y n hnBlt)
            ⟨hnpos', hs⟩
        simpa [pow_succ', Equiv.Perm.mul_apply] using
          hstep hrel hnotA hnotB

theorem finiteFirstReturnTime_eq_of_aligned_first
    (sigma : Equiv.Perm A) (tau : Equiv.Perm B)
    (selectedA : A -> Prop) (selectedB : B -> Prop)
    [DecidablePred selectedA] [DecidablePred selectedB]
    (R : A -> B -> Prop)
    (hselected : forall {a b}, R a b ->
      (selectedA a <-> selectedB b))
    (hstep : forall {a b}, R a b -> Not (selectedA a) ->
      Not (selectedB b) -> R (sigma a) (tau b))
    (x : {a : A // selectedA a}) (y : {b : B // selectedB b})
    (hfirst : R (sigma x.1) (tau y.1)) :
    finiteFirstReturnTime sigma selectedA x =
      finiteFirstReturnTime tau selectedB y := by
  let m := finiteFirstReturnTime sigma selectedA x
  let n := finiteFirstReturnTime tau selectedB y
  rcases le_total m n with hmn | hnm
  · have hrel := finiteRelated_until_firstReturn sigma tau
      selectedA selectedB R hstep x y hfirst m
      (finiteFirstReturnTime_pos sigma selectedA x) (by rfl) hmn
    have hselectedB : selectedB ((tau ^ m) y.1) :=
      (hselected hrel).mp
        (finiteFirstReturnTime_selected sigma selectedA x)
    have hnm' : n <= m := Nat.find_min'
      (finiteReturnWitness tau selectedB y)
      ⟨finiteFirstReturnTime_pos sigma selectedA x, hselectedB⟩
    exact Nat.le_antisymm hmn hnm'
  · have hrel := finiteRelated_until_firstReturn sigma tau
      selectedA selectedB R hstep x y hfirst n
      (finiteFirstReturnTime_pos tau selectedB y) hnm (by rfl)
    have hselectedA : selectedA ((sigma ^ n) x.1) :=
      (hselected hrel).mpr
        (finiteFirstReturnTime_selected tau selectedB y)
    have hmn' : m <= n := Nat.find_min'
      (finiteReturnWitness sigma selectedA x)
      ⟨finiteFirstReturnTime_pos tau selectedB y, hselectedA⟩
    exact Nat.le_antisymm hmn' hnm

theorem finiteFirstReturn_related_of_aligned_first
    (sigma : Equiv.Perm A) (tau : Equiv.Perm B)
    (selectedA : A -> Prop) (selectedB : B -> Prop)
    [DecidablePred selectedA] [DecidablePred selectedB]
    (R : A -> B -> Prop)
    (hselected : forall {a b}, R a b ->
      (selectedA a <-> selectedB b))
    (hstep : forall {a b}, R a b -> Not (selectedA a) ->
      Not (selectedB b) -> R (sigma a) (tau b))
    (x : {a : A // selectedA a}) (y : {b : B // selectedB b})
    (hfirst : R (sigma x.1) (tau y.1)) :
    R (finiteFirstReturn sigma selectedA x).1
      (finiteFirstReturn tau selectedB y).1 := by
  let htime := finiteFirstReturnTime_eq_of_aligned_first sigma tau
    selectedA selectedB R hselected hstep x y hfirst
  unfold finiteFirstReturn
  change R ((sigma ^ finiteFirstReturnTime sigma selectedA x) x.1)
    ((tau ^ finiteFirstReturnTime tau selectedB y) y.1)
  rw [← htime]
  apply finiteRelated_until_firstReturn sigma tau selectedA selectedB
    R hstep x y hfirst
  · exact finiteFirstReturnTime_pos sigma selectedA x
  · rfl
  · rw [htime]

end Related

end

end StatMech.FrontierD
