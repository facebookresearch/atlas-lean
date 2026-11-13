/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Torsor.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

section

namespace MetaMathlibExt

/-- Rotation of a tuple by `k` positions (forward shift of indices). -/
private def rotShift (G : Type*) (n : ℕ) [NeZero n]
    (k : ZMod n) (x : Fin n → G) : Fin n → G :=
  fun i => x ⟨(i.val + k.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- Modular arithmetic helper for shift composition. -/
private lemma mod_add_wrap (i a b n : ℕ) : (i + (a + b) % n) % n = ((i + a) % n + b) % n := by
  have e1 : (i + (a + b) % n) % n = (i + (a + b)) % n := by
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have e2 : ((i + a) % n + b) % n = ((i + a) + b) % n := by
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have hassoc : i + (a + b) = (i + a) + b := by ring
  rw [e1, e2, hassoc]

private lemma rotShift_zero (G : Type*)
    (n : ℕ) [NeZero n] (x : Fin n → G) : rotShift G n 0 x = x := by
  funext i
  have hval : (i.val + (0 : ZMod n).val) % n = i.val := by
    rw [ZMod.val_zero, Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
  change x ⟨(i.val + (0 : ZMod n).val) % n, _⟩ = x i
  exact congrArg x (Fin.ext hval)

private lemma rotShift_add (G : Type*)
    (n : ℕ) [NeZero n] (k l : ZMod n) (x : Fin n → G) :
    rotShift G n (k + l) x = rotShift G n k (rotShift G n l x) := by
  funext i
  have hval : (i.val + (k + l).val) % n
      = (((i.val + k.val) % n) + l.val) % n := by
    rw [ZMod.val_add]
    exact mod_add_wrap i.val k.val l.val n
  change x ⟨(i.val + (k + l).val) % n, _⟩
    = x ⟨(((i.val + k.val) % n) + l.val) % n, _⟩
  exact congrArg x (Fin.ext hval)

/-- The rotated tuple, as a list, is `drop ++ take`. -/
private lemma rotShift_list_eq (G : Type*)
    (n : ℕ) [NeZero n] (k : ZMod n) (x : Fin n → G) :
    List.ofFn (rotShift G n k x)
      = (List.ofFn x).drop k.val ++ (List.ofFn x).take k.val := by
  have hkle : k.val ≤ n := Nat.le_of_lt (ZMod.val_lt k)
  have hnpos : 0 < n := NeZero.pos n
  refine List.ext_getElem ?_ ?_
  · rw [List.length_ofFn, List.length_append, List.length_drop, List.length_take,
      List.length_ofFn, Nat.min_eq_left hkle, Nat.sub_add_cancel hkle]
  · intro j h1 h2
    have h1n : j < n := by simpa [List.length_ofFn] using h1
    have hLHS : (List.ofFn (rotShift G n k x))[j]'h1
        = x ⟨(j + k.val) % n, Nat.mod_lt _ hnpos⟩ :=
      List.getElem_ofFn h1
    rw [hLHS]
    by_cases hj : j < ((List.ofFn x).drop k.val).length
    · have hjlt : j < n - k.val := by
        simpa [List.length_drop, List.length_ofFn] using hj
      rw [List.getElem_append_left hj, List.getElem_drop, List.getElem_ofFn]
      have hlt : j + k.val < n := by omega
      have hmod : (j + k.val) % n = k.val + j := by
        rw [Nat.mod_eq_of_lt hlt]; omega
      change x ⟨(j + k.val) % n, _⟩ = x ⟨k.val + j, _⟩
      exact congrArg x (Fin.ext hmod)
    · have hdrop : ((List.ofFn x).drop k.val).length = n - k.val := by
        rw [List.length_drop, List.length_ofFn]
      have hle : ((List.ofFn x).drop k.val).length ≤ j := not_lt.mp hj
      rw [List.getElem_append_right hle, List.getElem_take, List.getElem_ofFn]
      have hmod : (j + k.val) % n = j - ((List.ofFn x).drop k.val).length := by
        have h2n : j < n := by
          have hlen : ((List.ofFn x).drop k.val
            ++ (List.ofFn x).take k.val).length = n := by
            rw [List.length_append, hdrop, List.length_take, List.length_ofFn,
              Nat.min_eq_left hkle, Nat.sub_add_cancel hkle]
          omega
        have heq : j + k.val = n + (j - ((List.ofFn x).drop k.val).length) := by
          omega
        have hlt2 : j - ((List.ofFn x).drop k.val).length < n := by omega
        rw [heq, Nat.add_comm n _, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
      change x ⟨(j + k.val) % n, _⟩ = x ⟨j - ((List.ofFn x).drop k.val).length, _⟩
      exact congrArg x (Fin.ext hmod)

/-- Rotation preserves the identity-product property (rotated product is conjugate). -/
private lemma rotShift_prod_eq_one (G : Type*) [Group G]
    (n : ℕ) [NeZero n] (k : ZMod n) (x : Fin n → G) :
    (List.ofFn (rotShift G n k x)).prod = 1 ↔ (List.ofFn x).prod = 1 := by
  have hcomm : ∀ a b : G, a * b = 1 ↔ b * a = 1 := by
    intro a b
    constructor
    · intro h
      have h1 : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [h1, mul_inv_cancel]
    · intro h
      have h1 : b = a⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [h1, mul_inv_cancel]
  have hPx : (List.ofFn x).prod
      = ((List.ofFn x).take k.val).prod * ((List.ofFn x).drop k.val).prod := by
    conv_lhs => rw [← List.take_append_drop k.val (List.ofFn x), List.prod_append]
  rw [rotShift_list_eq G n k x, List.prod_append, hPx]
  exact hcomm _ _

/-- The rotation action as a function on identity-product tuples. -/
private def rotVAddFun (G : Type*) [Group G] (n : ℕ) [NeZero n]
    (k : ZMod n) (x : {x : Fin n → G // (List.ofFn x).prod = 1}) :
    {x : Fin n → G // (List.ofFn x).prod = 1} :=
  ⟨rotShift G n k x.val, (rotShift_prod_eq_one G n k x.val).mpr x.prop⟩

private instance rotVAddInst (G : Type*) [Group G] (n : ℕ)
    [NeZero n] :
    VAdd (ZMod n) {x : Fin n → G // (List.ofFn x).prod = 1} :=
  ⟨rotVAddFun G n⟩

private instance rotAddSemigroupActionInst (G : Type*) [Group G]
    (n : ℕ) [NeZero n] :
    AddSemigroupAction (ZMod n) {x : Fin n → G // (List.ofFn x).prod = 1} where
  add_vadd := fun k l x => Subtype.ext (rotShift_add G n k l x.val)

private instance rotAddActionInst (G : Type*) [Group G]
    (n : ℕ) [NeZero n] :
    AddAction (ZMod n) {x : Fin n → G // (List.ofFn x).prod = 1} where
  zero_vadd := fun x => Subtype.ext (rotShift_zero G n x.val)

private instance rotFintype (G : Type*) [Group G] [Fintype G] [DecidableEq G] (n : ℕ) :
    Fintype {x : Fin n → G // (List.ofFn x).prod = 1} := by
  classical
  exact Subtype.fintype _

private instance rotFixedByFintype (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (n : ℕ) [NeZero n] (k : ZMod n) :
    Fintype ↥(AddAction.fixedBy {x : Fin n → G // (List.ofFn x).prod = 1} k) := by
  classical
  exact Subtype.fintype _

private instance orbRelSetoid (G : Type*) [Group G]
    (n : ℕ) [NeZero n] :
    Setoid {x : Fin n → G // (List.ofFn x).prod = 1} :=
  AddAction.orbitRel (ZMod n) {x : Fin n → G // (List.ofFn x).prod = 1}

private noncomputable instance rotQuotFintype (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (n : ℕ) [NeZero n] :
    Fintype (Quotient (AddAction.orbitRel (ZMod n)
      {x : Fin n → G // (List.ofFn x).prod = 1})) := by
  classical
  exact Quotient.fintype _

/-- The rotation-orbit set of a tuple, in the form used by the theorem statement. -/
private def orbSet (G : Type*) (n : ℕ) [NeZero n]
    (x : Fin n → G) : Set (Fin n → G) :=
  {y | ∃ m : ℕ, m < n ∧ ∀ i : Fin n, y i = x ⟨(i.val + m) % n, Nat.mod_lt _ (NeZero.pos n)⟩}

/-- Shifting shrinks the orbit set. -/
private lemma orbSet_mono (G : Type*) [Group G]
    (n : ℕ) [NeZero n] (k : ZMod n)
    (x : {x : Fin n → G // (List.ofFn x).prod = 1}) :
    orbSet G n (k +ᵥ x).val ⊆ orbSet G n x.val := by
  intro y hy
  obtain ⟨m, hmn, hm⟩ := hy
  refine ⟨(m + k.val) % n, Nat.mod_lt _ (NeZero.pos n), fun i => ?_⟩
  have h1 : y i = (k +ᵥ x).val ⟨(i.val + m) % n, Nat.mod_lt _ (NeZero.pos n)⟩ := hm _
  have h2 : ∀ j : Fin n, (k +ᵥ x).val j
      = x.val ⟨(j.val + k.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩ :=
    fun j => rfl
  rw [h1, h2]
  refine congrArg x.val (Fin.ext ?_)
  exact (mod_add_wrap i.val m k.val n).symm

/-- Shifting preserves the orbit set. -/
private lemma orbSet_shift_eq (G : Type*) [Group G]
    (n : ℕ) [NeZero n] (k : ZMod n)
    (x : {x : Fin n → G // (List.ofFn x).prod = 1}) :
    orbSet G n (k +ᵥ x).val = orbSet G n x.val := by
  apply Set.Subset.antisymm (orbSet_mono G n k x)
  have hback : ((-k) +ᵥ (k +ᵥ x)) = x := by
    rw [← add_vadd, neg_add_cancel, zero_vadd]
  have hsub := orbSet_mono G n (-k) (k +ᵥ x)
  rwa [hback] at hsub

/-- Every tuple lies in its own orbit set. -/
private lemma orbSet_mem_self (G : Type*) [Group G]
    (n : ℕ) [NeZero n]
    (x : {x : Fin n → G // (List.ofFn x).prod = 1}) :
    x.val ∈ orbSet G n x.val := by
  refine ⟨0, NeZero.pos n, fun i => ?_⟩
  have hval : (i.val + 0) % n = i.val := by
    rw [Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
  change x.val i = x.val ⟨(i.val + 0) % n, _⟩
  exact congrArg x.val (Fin.ext hval.symm)

/-- Orbit sets respect the orbit relation. -/
private lemma orbSet_congr (G : Type*) [Group G]
    (n : ℕ) [NeZero n]
    (x y : {x : Fin n → G // (List.ofFn x).prod = 1})
    (h : x ∈ AddAction.orbit (ZMod n) y) :
    orbSet G n x.val = orbSet G n y.val := by
  obtain ⟨g, hg⟩ := AddAction.mem_orbit_iff.mp h
  subst hg
  exact orbSet_shift_eq G n g y

/-- The quotient-to-orbit-set map. -/
private def neckQuot (G : Type*) [Group G] (n : ℕ) [NeZero n] :
    Quotient (AddAction.orbitRel (ZMod n)
      {x : Fin n → G // (List.ofFn x).prod = 1}) → Set (Fin n → G) :=
  fun q => orbSet G n q.out.val

private lemma neckQuot_injective (G : Type*) [Group G]
    (n : ℕ) [NeZero n] : Function.Injective (neckQuot G n) := by
  intro q1 q2 hq
  have hq' : orbSet G n (Quotient.out q1).val
      = orbSet G n (Quotient.out q2).val := hq
  have hmem : (Quotient.out q2).val ∈ orbSet G n (Quotient.out q1).val := by
    have hself := orbSet_mem_self G n (Quotient.out q2)
    rwa [← hq'] at hself
  obtain ⟨m, hmn, hm⟩ := hmem
  have hkval : ((m : ZMod n)).val = m := ZMod.val_natCast_of_lt hmn
  have hact : ((m : ZMod n) +ᵥ (Quotient.out q1)) = Quotient.out q2 := by
    apply Subtype.ext
    funext i
    show ((m : ZMod n) +ᵥ Quotient.out q1).val i = (Quotient.out q2).val i
    have hL : ((m : ZMod n) +ᵥ (Quotient.out q1)).val i
        = (Quotient.out q1).val ⟨(i.val + m) % n, Nat.mod_lt _ (NeZero.pos n)⟩ := by
      change (Quotient.out q1).val ⟨(i.val + ((m : ZMod n)).val) % n, _⟩ = _
      have hvaleq : (i.val + ((m : ZMod n)).val) % n = (i.val + m) % n := by
        rw [hkval]
      exact congrArg (Quotient.out q1).val (Fin.ext hvaleq)
    rw [hL]
    exact (hm i).symm
  have hrel : (AddAction.orbitRel (ZMod n)
      {x : Fin n → G // (List.ofFn x).prod = 1}).r
      (Quotient.out q2) (Quotient.out q1) :=
    AddAction.mem_orbit_iff.mpr ⟨(m : ZMod n), hact⟩
  have hqq : (⟦Quotient.out q1⟧ : Quotient _) = ⟦Quotient.out q2⟧ :=
    (Quot.sound hrel).symm
  have e1 : q1 = (⟦Quotient.out q1⟧ : Quotient _) := (Quotient.out_eq q1).symm
  have e2 : q2 = (⟦Quotient.out q2⟧ : Quotient _) := (Quotient.out_eq q2).symm
  rw [e1, e2]
  exact hqq

/-- The described set of necklaces is the range of `neckQuot`. -/
private lemma neck_range (G : Type*) [Group G]
    (n : ℕ) [NeZero n] (S : Set (Set (Fin n → G)))
    (hS : S = {O : Set (Fin n → G) | ∃ x : Fin n → G, (List.ofFn x).prod = 1 ∧
      O = orbSet G n x}) :
    S = neckQuot G n '' Set.univ := by
  rw [hS]
  ext O
  constructor
  · rintro ⟨x, hx, hO⟩
    let q : Quotient (AddAction.orbitRel (ZMod n)
        {x : Fin n → G // (List.ofFn x).prod = 1}) :=
      ⟦(⟨x, hx⟩ : {x : Fin n → G // (List.ofFn x).prod = 1})⟧
    refine ⟨q, Set.mem_univ _, ?_⟩
    have hex : (Quotient.out q :
        {x : Fin n → G // (List.ofFn x).prod = 1}) ≈ ⟨x, hx⟩ :=
      Quotient.exact (Quotient.out_eq _)
    have heq := orbSet_congr G n _ _ hex
    change orbSet G n (Quotient.out q).val = O
    rw [heq]
    exact hO.symm
  · rintro ⟨q, _, hO⟩
    exact ⟨(Quotient.out q).val, (Quotient.out q).prop, hO.symm⟩

/-- Cast of a mod is the original element in `ZMod n`. -/
private lemma cast_mod_eq (n m : ℕ) : (((m % n : ℕ)) : ZMod n) = ((m : ℕ) : ZMod n) :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.mod_modEq m n)

/-- Shifting by a multiple of `d` preserves the mod-`d` class, through a mod-`n` wrap. -/
private lemma mod_shift_eq (i k d n : ℕ) (hdvd_n : d ∣ n) (hdvd_k : d ∣ k) :
    ((i + k) % n) % d = i % d := by
  rw [Nat.mod_mod_of_dvd _ hdvd_n]
  have hk0 : k % d = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd_k
  conv_lhs => rw [Nat.add_mod, hk0, Nat.add_zero, Nat.mod_mod]

/-- The additive order of `k : ZMod n` is `n / gcd n k.val`. -/
private lemma addOrderOf_eq (n : ℕ) [NeZero n] (k : ZMod n) :
    addOrderOf k = n / Nat.gcd n k.val := by
  have hnpos : 0 < n := NeZero.pos n
  have hddpos : 0 < Nat.gcd n k.val := Nat.gcd_pos_of_pos_left _ hnpos
  have hcop0 := Nat.coprime_div_gcd_div_gcd hddpos (m := n) (n := k.val)
  obtain ⟨nv, hnv⟩ := Nat.gcd_dvd_left n k.val
  obtain ⟨kv, hkv⟩ := Nat.gcd_dvd_right n k.val
  set G := Nat.gcd n k.val with hG
  have hnv_eq : n / G = nv := by
    have hmul : G * nv / G = nv := by
      rw [mul_comm G nv]
      exact Nat.mul_div_cancel _ hddpos
    rwa [← hnv] at hmul
  have hkv_eq : k.val / G = kv := by
    have hmul : G * kv / G = kv := by
      rw [mul_comm G kv]
      exact Nat.mul_div_cancel _ hddpos
    rwa [← hkv] at hmul
  have hcop : Nat.Coprime nv kv := by
    rwa [hnv_eq, hkv_eq] at hcop0
  rw [hnv_eq]
  apply Nat.dvd_antisymm
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    have hcast : nv • k = (((nv * k.val : ℕ)) : ZMod n) := by
      rw [nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [hcast, ZMod.natCast_eq_zero_iff]
    have e1 : nv * k.val = nv * (G * kv) := by rw [hkv]
    have e2 : nv * (G * kv) = (G * nv) * kv := by ring
    have e3 : (G * nv) * kv = n * kv := by rw [← hnv]
    exact ⟨kv, by rw [e1, e2, e3]⟩
  · set t := addOrderOf k with ht
    have h0 : t • k = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp dvd_rfl
    have hcast : t • k
        = (((t * k.val : ℕ)) : ZMod n) := by
      rw [nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_zmod_val]
    have h0' : n ∣ t * k.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      rwa [hcast] at h0
    rw [hkv, hnv] at h0'
    have h1 : nv ∣ t * kv := by
      have hring : t * (G * kv)
          = G * (t * kv) := by ring
      rw [hring] at h0'
      exact (Nat.mul_dvd_mul_iff_left hddpos).mp h0'
    exact hcop.dvd_of_dvd_mul_right h1

/-- Bézout: the gcd is a multiple of `k` in `ZMod n`. -/
private lemma bezout_eq (n : ℕ) [NeZero n] (k : ZMod n) :
    ((Nat.gcd n k.val : ℕ) : ZMod n)
      = ((Nat.gcdB n k.val : ℤ) : ZMod n) * k := by
  have h := Nat.gcd_eq_gcd_ab n k.val
  have h2 := congrArg (fun z : ℤ => (z : ZMod n)) h
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul, zero_add] at h2
  rw [ZMod.natCast_zmod_val] at h2
  exact h2.trans (mul_comm _ _)

/-- A tuple fixed under single `c`-steps is fixed under any number of steps. -/
private lemma iter_fixed (G : Type*)
    (n : ℕ) [NeZero n] (c : ℕ) (x : Fin n → G)
    (hfix : ∀ j : Fin n, x ⟨(j.val + c) % n, Nat.mod_lt _ (NeZero.pos n)⟩ = x j)
    (t u : ℕ) (hu : u < n) :
    x ⟨(u + t * c) % n, Nat.mod_lt _ (NeZero.pos n)⟩ = x ⟨u, hu⟩ := by
  induction t with
  | zero =>
    have key0 : (u + 0 * c) % n = u := by
      rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt hu]
    exact congrArg x (Fin.ext key0)
  | succ t ih =>
    have hstep : (u + (t * c + c)) % n = ((u + t * c) % n + c) % n := by
      have e : ((u + t * c) % n + c) % n = ((u + t * c) + c) % n := by
        conv_lhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have hassoc : u + (t * c + c) = (u + t * c) + c := by ring
      rw [e, hassoc]
    have htc : (t + 1) * c = t * c + c := by ring
    have key : (u + (t + 1) * c) % n = ((u + t * c) % n + c) % n := by
      rw [htc]; exact hstep
    calc x ⟨(u + (t + 1) * c) % n, Nat.mod_lt _ (NeZero.pos n)⟩
        = x ⟨((u + t * c) % n + c) % n, Nat.mod_lt _ (NeZero.pos n)⟩ :=
          congrArg x (Fin.ext key)
      _ = x ⟨(u + t * c) % n, Nat.mod_lt _ (NeZero.pos n)⟩ :=
          hfix ⟨(u + t * c) % n, Nat.mod_lt _ (NeZero.pos n)⟩
      _ = x ⟨u, hu⟩ := ih

/-- A tuple fixed under `k`-shifts is determined by its values on `0 .. d-1`. -/
private lemma path_lemma (G : Type*)
    (n : ℕ) [NeZero n] (k : ZMod n) (x : Fin n → G)
    (hfix : ∀ j : Fin n, x ⟨(j.val + k.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩
      = x j) :
    ∀ i : Fin n, x i = x ⟨i.val % Nat.gcd n k.val,
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.gcd_pos_of_pos_left _ (NeZero.pos n)))
        (Nat.gcd_le_left _ (NeZero.pos n))⟩ := by
  have hnpos : 0 < n := NeZero.pos n
  set dd := Nat.gcd n k.val with hdd
  have hddpos : 0 < dd := Nat.gcd_pos_of_pos_left _ hnpos
  have hddle : dd ≤ n := Nat.gcd_le_left _ hnpos
  have hbez : ((dd : ℕ) : ZMod n) = ((Nat.gcdB n k.val : ℤ) : ZMod n) * k := by
    rw [hdd]
    exact bezout_eq n k
  intro i
  have hj0lt : i.val % dd < n :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hddpos) hddle
  set s : ZMod n := ((i.val / dd : ℕ) : ZMod n) * ((Nat.gcdB n k.val : ℤ) : ZMod n)
    with hs
  have hclaim : ((i.val : ℕ) : ZMod n)
      = ((i.val % dd : ℕ) : ZMod n) + s * k := by
    have hdecomp : i.val = i.val % dd + dd * (i.val / dd) := by
      have h := Nat.mod_add_div i.val dd
      omega
    conv_lhs => rw [hdecomp]
    push_cast
    rw [hbez, hs]
    ring
  have hstep := iter_fixed G n k.val x hfix s.val (i.val % dd) hj0lt
  have hXcast : (i.val % dd + s.val * k.val) % n = i.val := by
    have h1 : ((((i.val % dd + s.val * k.val) % n : ℕ))) = ((i.val : ℕ) : ZMod n) := by
      have h1a : ((((i.val % dd + s.val * k.val) % n : ℕ)) : ZMod n)
          = ((i.val % dd : ℕ) : ZMod n) + s * k := by
        rw [cast_mod_eq]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      rw [h1a]
      exact hclaim.symm
    have hv1 := ZMod.val_natCast_of_lt (Nat.mod_lt _ hnpos :
      (i.val % dd + s.val * k.val) % n < n)
    have hv2 := ZMod.val_natCast_of_lt i.isLt
    have hcon := congrArg ZMod.val h1
    rwa [hv1, hv2] at hcon
  have hfin : (⟨(i.val % dd + s.val * k.val) % n,
      Nat.mod_lt _ hnpos⟩ : Fin n) = ⟨i.val, i.isLt⟩ := Fin.ext hXcast
  rw [hfin] at hstep
  exact hstep

/-- Any transversal tuple is fixed under `k`-shifts. -/
private lemma transversal_fixed (G : Type*)
    (n : ℕ) (k : ZMod n) (d : ℕ) (hd : 0 < d)
    (hdvd_n : d ∣ n) (hdvd_k : d ∣ k.val) (a : Fin d → G) :
    ∀ i : Fin n, a ⟨((i.val + k.val) % n) % d, Nat.mod_lt _ hd⟩
      = a ⟨i.val % d, Nat.mod_lt _ hd⟩ := by
  intro i
  exact congrArg a (Fin.ext (mod_shift_eq i.val k.val d n hdvd_n hdvd_k))

/-- Product over a periodic tuple equals a power. -/
private lemma block_prod (G : Type*) [Group G]
    (d : ℕ) (hd : 0 < d) (e : ℕ) (a : Fin d → G) :
    ∀ (n : ℕ) (x : Fin n → G), e * d = n →
    (∀ i, x i = a ⟨i.val % d, Nat.mod_lt _ hd⟩) →
    (List.ofFn x).prod = ((List.ofFn a).prod) ^ e := by
  induction e with
  | zero =>
    intro n x hn h
    have hn0 : n = 0 := by
      have h0 : 0 * d = n := hn
      rw [Nat.zero_mul] at h0
      exact h0.symm
    subst hn0
    rw [pow_zero]
    have hlen : (List.ofFn x).length = 0 := by rw [List.length_ofFn]
    rw [List.length_eq_zero_iff.mp hlen, List.prod_nil]
  | succ e ih =>
    intro n x hn h
    have hdecomp : (e + 1) * d = e * d + d := by ring
    have hn2 : n = e * d + d := hn.symm.trans hdecomp
    have hle : d ≤ n := by
      have h1 : d ≤ e * d + d := Nat.le_add_left _ _
      rwa [← hn2] at h1
    have htake : (List.ofFn x).take d = List.ofFn a := by
      refine List.ext_getElem ?_ ?_
      · rw [List.length_take, List.length_ofFn, List.length_ofFn,
          Nat.min_eq_left hle]
      · intro j h1 h2
        have hj : j < d := by
          have h1' := h1
          rwa [List.length_take, List.length_ofFn, Nat.min_eq_left hle] at h1'
        rw [List.getElem_take, List.getElem_ofFn, List.getElem_ofFn]
        have hxj := h ⟨j, by omega⟩
        have hmod : j % d = j := Nat.mod_eq_of_lt hj
        have hfin : (⟨j % d, Nat.mod_lt _ hd⟩ : Fin d) = ⟨j, by omega⟩ :=
          Fin.ext hmod
        rw [hfin] at hxj
        exact hxj
    set y : Fin (e * d) → G := fun i => x ⟨i.val + d, by
      have hbd := i.isLt
      omega⟩ with hydef
    have hdrop : (List.ofFn x).drop d = List.ofFn y := by
      refine List.ext_getElem ?_ ?_
      · rw [List.length_drop, List.length_ofFn, List.length_ofFn, hn2,
          Nat.add_sub_cancel]
      · intro j h1 h2
        have hj2 : j < e * d := by simpa [List.length_ofFn] using h2
        rw [List.getElem_drop, List.getElem_ofFn, List.getElem_ofFn]
        have hdeq : d + j = j + d := by omega
        change x ⟨d + j, _⟩ = y ⟨j, _⟩
        change x ⟨d + j, _⟩ = x ⟨j + d, _⟩
        exact congrArg x (Fin.ext hdeq)
    have hy : ∀ i, y i = a ⟨i.val % d, Nat.mod_lt _ hd⟩ := by
      intro i
      change x ⟨i.val + d, _⟩ = a ⟨i.val % d, _⟩
      have hxi := h ⟨i.val + d, by
        have hbd := i.isLt
        omega⟩
      have hmodd : (i.val + d) % d = i.val % d := Nat.add_mod_right _ _
      have hfin : (⟨(i.val + d) % d, Nat.mod_lt _ hd⟩ : Fin d)
          = ⟨i.val % d, Nat.mod_lt _ hd⟩ := Fin.ext hmodd
      rw [hfin] at hxi
      exact hxi
    have ih' := ih (e * d) y rfl hy
    have hprod : (List.ofFn x).prod
        = ((List.ofFn a).prod) * ((List.ofFn y).prod) := by
      conv_lhs => rw [← List.take_append_drop d (List.ofFn x), List.prod_append,
        htake, hdrop]
    rw [hprod, ih', pow_succ']

/-- Updating the last coordinate right-multiplies the product. -/
private lemma prod_update_last (G : Type*) [Group G]
    (d : ℕ) (hd : 0 < d) (a : Fin d → G) (t : G) :
    (List.ofFn (Function.update a ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (a ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * t))).prod
    = (List.ofFn a).prod * t := by
  have htake_len : ((List.ofFn a).take (d - 1)).length = d - 1 := by
    rw [List.length_take, List.length_ofFn, Nat.min_eq_left (Nat.sub_le _ _)]
  have key : ∀ v : G, List.ofFn
      (Function.update a ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ v)
      = (List.ofFn a).take (d - 1) ++ [v] := by
    intro v
    refine List.ext_getElem ?_ ?_
    · rw [List.length_ofFn, List.length_append, List.length_take,
        List.length_ofFn, List.length_singleton,
        Nat.min_eq_left (Nat.sub_le _ _), Nat.sub_add_cancel hd]
    · intro j h1 h2
      by_cases hj : j < d - 1
      · have hj' : j < ((List.ofFn a).take (d - 1)).length := by omega
        have hne : (⟨j, by omega⟩ : Fin d)
            ≠ ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ := by
          intro hcon
          have hvv : j = d - 1 := Fin.ext_iff.mp hcon
          omega
        rw [List.getElem_append_left hj', List.getElem_take, List.getElem_ofFn,
          List.getElem_ofFn, Function.update_of_ne hne]
      · have hlen2 : ((List.ofFn a).take (d - 1) ++ [v]).length = d := by
          rw [List.length_append, List.length_take, List.length_ofFn,
            List.length_singleton, Nat.min_eq_left (Nat.sub_le _ _),
            Nat.sub_add_cancel hd]
        have hjd : j = d - 1 := by
          have hjd' : j < d := by simpa [hlen2] using h2
          omega
        subst hjd
        have hle : ((List.ofFn a).take (d - 1)).length ≤ d - 1 := by omega
        rw [List.getElem_ofFn, Function.update_self,
          List.getElem_append_right hle, List.getElem_singleton]
  have e1 := key (a ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * t)
  have e2 := key (a ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩)
  have e3 : Function.update a ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (a ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩) = a :=
    Function.update_eq_self _ _
  rw [e3] at e2
  rw [e1, List.prod_append, List.prod_singleton]
  conv_rhs => rw [e2, List.prod_append, List.prod_singleton]
  rw [mul_assoc]

/-- All product-fibers over `Fin d → G` have the same card. -/
private lemma fiber_card_eq (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (d : ℕ) (hd : 0 < d) (g₀ : G) :
    Fintype.card {a : Fin d → G // (List.ofFn a).prod = g₀}
    = Fintype.card {a : Fin d → G // (List.ofFn a).prod = 1} := by
  classical
  refine Fintype.card_congr ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  · exact fun a => ⟨Function.update a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀⁻¹), by
      rw [prod_update_last G d hd a.val g₀⁻¹, a.prop, mul_inv_cancel]⟩
  · exact fun b => ⟨Function.update b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀), by
      rw [prod_update_last G d hd b.val g₀, b.prop, one_mul]⟩
  · intro a
    apply Subtype.ext
    change Function.update (Function.update a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀⁻¹))
      ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      ((Function.update a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀⁻¹))
      ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀) = a.val
    have hv1 : (Function.update a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
        (a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀⁻¹))
        ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
        = a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀⁻¹ :=
      Function.update_self _ _ _
    rw [hv1]
    have hval : (a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀⁻¹) * g₀
        = a.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [hval, Function.update_idem]
    exact Function.update_eq_self _ _
  · intro b
    apply Subtype.ext
    change Function.update (Function.update b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀))
      ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      ((Function.update b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
      (b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀))
      ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀⁻¹) = b.val
    have hv2 : (Function.update b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
        (b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀))
        ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
        = b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀ :=
      Function.update_self _ _ _
    rw [hv2]
    have hval : (b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * g₀) * g₀⁻¹
        = b.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ :=
      mul_inv_cancel_right _ _
    rw [hval, Function.update_idem]
    exact Function.update_eq_self _ _

/-- Counting tuples by their product: fibers over roots of unity. -/
private lemma fiber_count (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (d e : ℕ) (hd : 0 < d) :
    Fintype.card {a : Fin d → G // ((List.ofFn a).prod) ^ e = 1}
    = (Fintype.card G) ^ (d - 1) * Fintype.card {g : G // g ^ e = 1} := by
  classical
  have hCpos : 0 < Fintype.card G := Fintype.card_pos
  have hfib1 : Fintype.card {a : Fin d → G // (List.ofFn a).prod = 1}
      = (Fintype.card G) ^ (d - 1) := by
    have hmem : ∀ b : Fin d → G, (List.ofFn (Function.update b
        ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
        (b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * ((List.ofFn b).prod)⁻¹))).prod
        = 1 := by
      intro b
      rw [prod_update_last G d hd b ((List.ofFn b).prod)⁻¹, mul_inv_cancel]
    have hEquiv : ({a : Fin d → G // (List.ofFn a).prod = 1} × G)
        ≃ (Fin d → G) := by
      refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
      · exact fun p => Function.update p.1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
          (p.1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * p.2)
      · exact fun b => (⟨Function.update b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
          (b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * ((List.ofFn b).prod)⁻¹),
          hmem b⟩, (List.ofFn b).prod)
      · intro a
        obtain ⟨a1, t⟩ := a
        have hpi : (List.ofFn (Function.update a1.val
            ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
            (a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * t))).prod = t := by
          rw [prod_update_last G d hd a1.val t, a1.prop, one_mul]
        have hfst : Function.update (Function.update a1.val
            ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
            (a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * t))
            ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
            (((Function.update a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
            (a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * t))
            ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩) *
            ((List.ofFn (Function.update a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
            (a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * t))).prod)⁻¹)
            = a1.val := by
          rw [Function.update_self, hpi]
          have hv3 : (a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * t) * t⁻¹
              = a1.val ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ :=
            mul_inv_cancel_right _ _
          rw [hv3, Function.update_idem]
          exact Function.update_eq_self _ _
        rw [Prod.ext_iff]
        exact ⟨Subtype.ext hfst, hpi⟩
      · intro b
        change Function.update (Function.update b
            ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
            (b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * ((List.ofFn b).prod)⁻¹))
            ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
            ((Function.update b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
            (b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * ((List.ofFn b).prod)⁻¹))
            ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * (List.ofFn b).prod) = b
        have hv1 : (Function.update b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
            (b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * ((List.ofFn b).prod)⁻¹))
            ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
            = b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * ((List.ofFn b).prod)⁻¹ :=
          Function.update_self _ _ _
        rw [hv1]
        have hv2 : (b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ * ((List.ofFn b).prod)⁻¹)
            * (List.ofFn b).prod = b ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
        rw [hv2, Function.update_idem]
        exact Function.update_eq_self _ _
    have hcard := Fintype.card_congr hEquiv
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at hcard
    have hCd : (Fintype.card G) ^ d
        = (Fintype.card G) ^ (d - 1) * Fintype.card G := by
      conv_lhs => rw [← Nat.sub_add_cancel hd, pow_succ]
    rw [hCd] at hcard
    exact mul_right_cancel₀ (ne_of_gt hCpos) hcard
  have hmaps : Set.MapsTo (fun a : Fin d → G => (List.ofFn a).prod)
      ↑(Finset.univ.filter
        (fun a : Fin d → G => ((List.ofFn a).prod) ^ e = 1))
      ↑(Finset.univ.filter (fun g : G => g ^ e = 1)) := by
    intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ,
      true_and] at ha ⊢
    exact ha
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter
      (fun a : Fin d → G => ((List.ofFn a).prod) ^ e = 1))
    (t := Finset.univ.filter (fun g : G => g ^ e = 1))
    (f := fun a : Fin d → G => (List.ofFn a).prod) hmaps
  have hfib : ∀ g ∈ Finset.univ.filter (fun g : G => g ^ e = 1),
      {a ∈ Finset.univ.filter
        (fun a : Fin d → G => ((List.ofFn a).prod) ^ e = 1)
        | (List.ofFn a).prod = g}.card
      = Fintype.card {a : Fin d → G // (List.ofFn a).prod = 1} := by
    intro g hg
    have hg1 : g ^ e = 1 := by
      have hgg := hg
      simpa [Finset.mem_filter] using hgg
    have hseq : {a ∈ Finset.univ.filter
          (fun a : Fin d → G => ((List.ofFn a).prod) ^ e = 1)
          | (List.ofFn a).prod = g}
        = Finset.univ.filter (fun a : Fin d → G => (List.ofFn a).prod = g) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rw [h]
        exact hg1
    have hce : Fintype.card {a : Fin d → G // (List.ofFn a).prod = g}
        = (Finset.univ.filter
          (fun a : Fin d → G => (List.ofFn a).prod = g)).card :=
      Fintype.card_ofFinset _ (fun a => by
        constructor
        · intro h
          exact (Finset.mem_filter.mp h).2
        · intro h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [hseq, ← hce]
    exact fiber_card_eq G d hd g
  have htot : (Finset.univ.filter
      (fun a : Fin d → G => ((List.ofFn a).prod) ^ e = 1)).card
      = (Finset.univ.filter (fun g : G => g ^ e = 1)).card
        * Fintype.card {a : Fin d → G // (List.ofFn a).prod = 1} := by
    rw [hsum, Finset.sum_congr rfl (fun g hg => hfib g hg), Finset.sum_const]
    simp only [nsmul_eq_mul, Nat.cast_id]
  have hLHS : Fintype.card {a : Fin d → G // ((List.ofFn a).prod) ^ e = 1}
      = (Finset.univ.filter
        (fun a : Fin d → G => ((List.ofFn a).prod) ^ e = 1)).card :=
    Fintype.card_ofFinset _ (fun a => by
      constructor
      · intro h
        exact (Finset.mem_filter.mp h).2
      · intro h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hRHS : (Finset.univ.filter (fun g : G => g ^ e = 1)).card
      = Fintype.card {g : G // g ^ e = 1} :=
    (Fintype.card_ofFinset (p := {g : G | g ^ e = 1}) _ (fun g => by
      constructor
      · intro h
        exact (Finset.mem_filter.mp h).2
      · intro h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)).symm
  rw [hLHS, htot, hfib1, hRHS, mul_comm]

/-- Fixed points of a rotation are transversal tuples with constrained product. -/
private def fixedBy_equiv_gcd (G : Type*) [Group G]
    (n : ℕ) [NeZero n] (k : ZMod n) :
    ↥(AddAction.fixedBy {x : Fin n → G // (List.ofFn x).prod = 1} k)
    ≃ {a : Fin (Nat.gcd n k.val) → G //
      ((List.ofFn a).prod) ^ (n / Nat.gcd n k.val) = 1} := by
  classical
  have hnpos : 0 < n := NeZero.pos n
  have hddpos : 0 < Nat.gcd n k.val := Nat.gcd_pos_of_pos_left _ hnpos
  have hddvd_n : Nat.gcd n k.val ∣ n := Nat.gcd_dvd_left _ _
  have hddvd_k : Nat.gcd n k.val ∣ k.val := Nat.gcd_dvd_right _ _
  have hdn : Nat.gcd n k.val ≤ n := Nat.gcd_le_left _ hnpos
  have hnde : n / Nat.gcd n k.val * Nat.gcd n k.val = n :=
    Nat.div_mul_cancel hddvd_n
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  · refine fun x => ⟨fun j => x.val.val ⟨j.val, Nat.lt_of_lt_of_le j.isLt hdn⟩,
      ?_⟩
    have hfix : ∀ j : Fin n,
        x.val.val ⟨(j.val + k.val) % n, Nat.mod_lt _ hnpos⟩ = x.val.val j := by
      have hkeq : k +ᵥ x.val = x.val := x.prop
      exact fun j => congrFun (congrArg Subtype.val hkeq) j
    have hshape : ∀ i : Fin n, x.val.val i
        = (fun j : Fin (Nat.gcd n k.val) =>
          x.val.val ⟨j.val, Nat.lt_of_lt_of_le j.isLt hdn⟩)
          ⟨i.val % Nat.gcd n k.val, Nat.mod_lt _ hddpos⟩ := by
      intro i
      change x.val.val i = x.val.val ⟨(i.val % Nat.gcd n k.val : ℕ), _⟩
      exact path_lemma G n k x.val.val hfix i
    have hblock := block_prod G (Nat.gcd n k.val) hddpos (n / Nat.gcd n k.val)
      (fun j : Fin (Nat.gcd n k.val) =>
        x.val.val ⟨j.val, Nat.lt_of_lt_of_le j.isLt hdn⟩)
      n x.val.val hnde hshape
    rw [← hblock]
    exact x.val.prop
  · refine fun a => ⟨⟨fun i : Fin n =>
      a.val ⟨i.val % Nat.gcd n k.val, Nat.mod_lt _ hddpos⟩, ?_⟩, ?_⟩
    · have hshape2 : ∀ i : Fin n,
          (fun i : Fin n => a.val ⟨i.val % Nat.gcd n k.val, Nat.mod_lt _ hddpos⟩)
            i = a.val ⟨i.val % Nat.gcd n k.val, Nat.mod_lt _ hddpos⟩ :=
        fun i => rfl
      have hblock2 := block_prod G _ hddpos _ a.val n _ hnde hshape2
      rw [hblock2]
      exact a.prop
    · apply Subtype.ext
      funext i
      change a.val ⟨((i.val + k.val) % n) % Nat.gcd n k.val, _⟩
        = a.val ⟨i.val % Nat.gcd n k.val, _⟩
      exact congrArg a.val
        (Fin.ext (mod_shift_eq i.val k.val _ n hddvd_n hddvd_k))
  · intro x
    have hfix : ∀ j : Fin n,
        x.val.val ⟨(j.val + k.val) % n, Nat.mod_lt _ hnpos⟩ = x.val.val j := by
      have hkeq : k +ᵥ x.val = x.val := x.prop
      exact fun j => congrFun (congrArg Subtype.val hkeq) j
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change x.val.val ⟨(i.val % Nat.gcd n k.val : ℕ), _⟩ = x.val.val i
    exact (path_lemma G n k x.val.val hfix i).symm
  · intro a
    apply Subtype.ext
    funext j
    change ((fun j : Fin (Nat.gcd n k.val) => (fun i : Fin n =>
      a.val ⟨i.val % Nat.gcd n k.val, Nat.mod_lt _ hddpos⟩)
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt hdn⟩)) j = a.val j
    have hmod : j.val % Nat.gcd n k.val = j.val := Nat.mod_eq_of_lt j.isLt
    change a.val ⟨j.val % Nat.gcd n k.val, _⟩ = a.val j
    exact congrArg a.val (Fin.ext hmod)

/-- Fixed-point count for a rotation. -/
private lemma card_fixedBy (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (n : ℕ) [NeZero n] (k : ZMod n) :
    Fintype.card ↥(AddAction.fixedBy {x : Fin n → G // (List.ofFn x).prod = 1} k)
    = (Fintype.card G) ^ (n / addOrderOf k - 1)
      * Fintype.card {g : G // g ^ addOrderOf k = 1} := by
  classical
  have he : addOrderOf k = n / Nat.gcd n k.val := addOrderOf_eq n k
  have hddvd_n : Nat.gcd n k.val ∣ n := Nat.gcd_dvd_left _ _
  have hn0 : n ≠ 0 := (NeZero.pos n).ne'
  have hde : n / addOrderOf k = Nat.gcd n k.val := by
    rw [he, Nat.div_div_self hddvd_n hn0]
  rw [hde, he, Fintype.card_congr (fixedBy_equiv_gcd G n k)]
  exact fiber_count G _ _ (Nat.gcd_pos_of_pos_left _ (NeZero.pos n))

/-- **Counting necklaces with identity product.** Let $G$ be a finite group and $n \ge 1$. For an
$n$-tuple $x = (x_0, \dots, x_{n-1}) \in G^n$ let its necklace be the set of its $n$ cyclic
rotations $(x_m, x_{m+1}, \dots, x_{m+n-1})$, $0 \le m < n$, with indices taken mod $n$. Then the
number of necklaces of tuples $x$ with $x_0 x_1 \cdots x_{n-1} = 1$ is
$$\frac{1}{n} \sum_{d \mid n} \varphi(n/d) \, r_{n/d}(G) \, |G|^{d-1},$$
where $\varphi$ is Euler's totient function and $r_k(G)$ is the number of $g \in G$ with
$g^k = 1$.

Source: Darij Grinberg and Peter Mao, "Necklaces over a Group with Identity Product,"
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 1 (`thm.main`), lines 186–195,
<https://cs.uwaterloo.ca/journals/JIS/VOL29/Grinberg/grinberg2.tex>. Identity-product tuples,
divisor-count notation, and necklaces defined at lines 140–180.

Proves `Wanted` entry `identity_product_necklace_count`.
-/
theorem identity_product_necklace_count (G : Type*) [Group G] [Fintype G]
  [DecidableEq G] (n : ℕ) (hn : 0 < n) :
  (Set.ncard
  { O : Set (Fin n → G) | ∃ x : Fin n → G, (List.ofFn x).prod = 1 ∧ O =
  { y | ∃ m : ℕ, m < n ∧ ∀ i : Fin n, y i = x ⟨(i.val + m) % n, Nat.mod_lt _ hn⟩ } } : ℚ) =
  (1 / (n : ℚ)) * Finset.sum (Nat.divisors n)
  (fun d => (Nat.totient (n / d) : ℚ) * (Fintype.card { g : G // g ^ (n / d) = 1 } : ℚ) *
  ((Fintype.card G : ℚ) ^ (d - 1))) := by
  classical
  have : NeZero n := ⟨hn.ne'⟩
  have hSeq : {O : Set (Fin n → G) | ∃ x : Fin n → G, (List.ofFn x).prod = 1 ∧
        O = {y | ∃ m : ℕ, m < n ∧ ∀ i : Fin n,
          y i = x ⟨(i.val + m) % n, Nat.mod_lt _ hn⟩}}
      = {O : Set (Fin n → G) | ∃ x : Fin n → G, (List.ofFn x).prod = 1 ∧
        O = orbSet G n x} := rfl
  rw [hSeq]
  have hSr := neck_range G n _ rfl
  rw [hSr, Set.ncard_image_of_injective _ (neckQuot_injective G n),
    Set.ncard_univ, Nat.card_eq_fintype_card]
  have hBurn := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
    (ZMod n) {x : Fin n → G // (List.ofFn x).prod = 1}
  rw [ZMod.card n] at hBurn
  have hmaps : ∀ k ∈ (Finset.univ : Finset (ZMod n)),
      addOrderOf k ∈ Nat.divisors n := by
    intro k _
    have hcd : addOrderOf k ∣ Fintype.card (ZMod n) := addOrderOf_dvd_card
    rw [ZMod.card n] at hcd
    exact Nat.mem_divisors.mpr ⟨hcd, hn.ne'⟩
  have hfib : ∀ e ∈ Nat.divisors n,
      (Finset.univ.filter (fun k : ZMod n => addOrderOf k = e)).card
        = e.totient := by
    intro e he
    have hdd : e ∣ n := (Nat.mem_divisors.mp he).1
    have hdiv : e ∣ Fintype.card (ZMod n) := by rwa [ZMod.card n]
    exact IsAddCyclic.card_addOrderOf_eq_totient hdiv
  have hgroup : (Finset.sum Finset.univ (fun k : ZMod n => Fintype.card
        ↥(AddAction.fixedBy {x : Fin n → G // (List.ofFn x).prod = 1} k)))
      = Finset.sum (Nat.divisors n) (fun e => (e.totient
        * Fintype.card {g : G // g ^ e = 1} * (Fintype.card G) ^ (n / e - 1))) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun k => Fintype.card ↥(AddAction.fixedBy
        {x : Fin n → G // (List.ofFn x).prod = 1} k))]
    refine Finset.sum_congr rfl (fun e he => ?_)
    have hinner : ∀ k ∈ Finset.univ.filter (fun k : ZMod n => addOrderOf k = e),
        Fintype.card ↥(AddAction.fixedBy
          {x : Fin n → G // (List.ofFn x).prod = 1} k)
        = (Fintype.card G) ^ (n / e - 1)
          * Fintype.card {g : G // g ^ e = 1} := by
      intro k hk
      have hke : addOrderOf k = e := (Finset.mem_filter.mp hk).2
      rw [card_fixedBy G n k, hke]
    rw [Finset.sum_congr rfl (fun k hk => hinner k hk), Finset.sum_const,
      hfib e he]
    simp only [nsmul_eq_mul, Nat.cast_id]
    ring
  have hreindex : (Finset.sum (Nat.divisors n) (fun e => (e.totient
        * Fintype.card {g : G // g ^ e = 1} * (Fintype.card G) ^ (n / e - 1))))
      = Finset.sum (Nat.divisors n) (fun d => ((Nat.totient (n / d))
        * Fintype.card {g : G // g ^ (n / d) = 1} * (Fintype.card G) ^ (d - 1))) := by
    refine Finset.sum_bij (fun e _ => n / e) ?maps ?inj ?surj ?val
    · intro e he
      exact Nat.mem_divisors.mpr
        ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp he).1, hn.ne'⟩
    · intro a ha b hb hab
      have ha' : a ∣ n := (Nat.mem_divisors.mp ha).1
      have hb' : b ∣ n := (Nat.mem_divisors.mp hb).1
      have e1 : n / (n / a) = a := Nat.div_div_self ha' hn.ne'
      have e2 : n / (n / b) = b := Nat.div_div_self hb' hn.ne'
      rw [hab] at e1
      exact e1.symm.trans e2
    · intro d hd
      have hd' : d ∣ n := (Nat.mem_divisors.mp hd).1
      refine ⟨n / d, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd', hn.ne'⟩, ?_⟩
      exact Nat.div_div_self hd' hn.ne'
    · intro e he
      rw [Nat.div_div_self (Nat.mem_divisors.mp he).1 hn.ne']
  have hQcard : Fintype.card (Quotient (AddAction.orbitRel (ZMod n)
        {x : Fin n → G // (List.ofFn x).prod = 1})) * n
      = Finset.sum (Nat.divisors n) (fun d => ((Nat.totient (n / d))
        * Fintype.card {g : G // g ^ (n / d) = 1} * (Fintype.card G) ^ (d - 1))) := by
    rw [← hBurn, hgroup, hreindex]
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : ((Fintype.card (Quotient (AddAction.orbitRel (ZMod n)
        {x : Fin n → G // (List.ofFn x).prod = 1})) : ℚ) * (n : ℚ))
      = Finset.sum (Nat.divisors n) (fun d => ((Nat.totient (n / d) : ℚ)
        * (Fintype.card {g : G // g ^ (n / d) = 1} : ℚ)
        * ((Fintype.card G : ℚ) ^ (d - 1)))) := by
    have h := congrArg (Nat.cast (R := ℚ)) hQcard
    simpa [Nat.cast_mul, Nat.cast_pow, Nat.cast_sum] using h
  calc ((Fintype.card (Quotient (AddAction.orbitRel (ZMod n)
        {x : Fin n → G // (List.ofFn x).prod = 1})) : ℚ))
      = (((Fintype.card (Quotient (AddAction.orbitRel (ZMod n)
        {x : Fin n → G // (List.ofFn x).prod = 1})) : ℚ) * (n : ℚ)) / (n : ℚ)) := by
        field_simp
    _ = _ := by rw [hc]; ring

end MetaMathlibExt

end
