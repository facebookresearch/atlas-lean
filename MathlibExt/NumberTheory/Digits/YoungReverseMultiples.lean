/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.List.Basic
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

private theorem foldl_acc (g : ℕ) (l : List ℕ) (acc : ℕ) :
    l.foldl (fun v d => v * g + d) acc =
      acc * g ^ l.length + Nat.ofDigits g l.reverse := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons]
    rw [ih (acc * g + a)]
    have hr : (a :: t).reverse = t.reverse ++ [a] := by simp
    rw [hr]
    simp only [Nat.ofDigits_append, List.length_reverse]
    simp only [Nat.ofDigits_cons, Nat.ofDigits_nil, Nat.mul_zero, Nat.add_zero]
    simp only [List.length_cons, pow_succ]
    ring

private theorem digitValue_eq (g : ℕ) (digits : List ℕ) :
    digits.foldl (fun v d => v * g + d) 0 = Nat.ofDigits g digits.reverse := by
  rw [foldl_acc]
  simp

private inductive IsCarryChain (g k : ℕ) : List ℕ → List ℕ → List ℕ → Prop
  | nil (c : ℕ) : IsCarryChain g k [] [] [c]
  | cons (x y c₀ c₁ : ℕ) (xs ys cs : List ℕ) :
      k * x + c₀ = y + c₁ * g →
      IsCarryChain g k xs ys (c₁ :: cs) →
      IsCarryChain g k (x :: xs) (y :: ys) (c₀ :: c₁ :: cs)

private theorem chain_getLast_cons (a b : ℕ) (l : List ℕ) :
    (a :: b :: l).getLast? = (b :: l).getLast? := by
  cases l with
  | nil => rfl
  | cons c l => simp [List.getLast?_cons_cons]

private theorem chain_balance (g k : ℕ) (xs ys cs : List ℕ)
    (h : IsCarryChain g k xs ys cs) :
    ∀ (cN : ℕ), cs.getLast? = some cN →
    ∀ (c₀ : ℕ) (rest : List ℕ), cs = c₀ :: rest →
      k * Nat.ofDigits g xs + c₀ =
        Nat.ofDigits g ys + cN * g ^ xs.length := by
  induction h with
  | nil c =>
    intro cN hlast c₀ rest hcs
    cases hcs with
    | refl =>
      simp only [List.getLast?_singleton] at hlast
      have heq : c = cN := Option.some_inj.mp hlast
      subst heq
      simp [Nat.ofDigits_nil]
  | cons x y c₀' c₁ xs ys cs hstep htail ih =>
    intro cN hlast c₀ rest hcs
    cases hcs with
    | refl =>
      simp only [Nat.ofDigits_cons, List.length_cons]
      have hlast' : (c₁ :: cs).getLast? = some cN := by
        have hgg := chain_getLast_cons c₀' c₁ cs
        rw [← hgg]
        exact hlast
      have ih' := ih cN hlast' c₁ cs rfl
      rw [pow_succ]
      have e1 : k * (x + g * Nat.ofDigits g xs) + c₀'
          = (y + c₁ * g) + g * (k * Nat.ofDigits g xs) := by rw [← hstep]; ring
      have e2 : y + g * Nat.ofDigits g ys + cN * (g ^ xs.length * g)
          = y + g * (Nat.ofDigits g ys + cN * g ^ xs.length) := by ring
      rw [e1, e2, ← ih']
      ring

private theorem chain_unique (g : ℕ) (hg : 0 < g) (k : ℕ) (xs ys cs1 : List ℕ)
    (h1 : IsCarryChain g k xs ys cs1) :
    ∀ (cs2 : List ℕ), IsCarryChain g k xs ys cs2 →
    ∀ (c₀ : ℕ) (t1 t2 : List ℕ), cs1 = c₀ :: t1 → cs2 = c₀ :: t2 → cs1 = cs2 := by
  induction h1 with
  | nil c =>
    intro cs2 h2 c₀ t1 t2 e1 e2
    cases h2 with
    | nil c' =>
      cases e1 with
      | refl =>
        cases e2 with
        | refl => rfl
  | cons x y c₀' c₁ xs ys cs hstep1 htail1 ih =>
    intro cs2 h2 c₀ t1 t2 e1 e2
    cases h2 with
    | cons x2 y2 d₀ d₁ xs2 ys2 cs2' hstep2 htail2 =>
      cases e1 with
      | refl =>
        cases e2 with
        | refl =>
          have e : c₁ * g = d₁ * g := by omega
          have hc : c₁ = d₁ := mul_right_cancel₀ (ne_of_gt hg) e
          subst hc
          have htail_eq := ih (c₁ :: cs2') htail2 c₁ cs cs2' rfl rfl
          rw [htail_eq]

private theorem chain_append (g k : ℕ) (xs1 ys1 cs1 : List ℕ)
    (h1 : IsCarryChain g k xs1 ys1 cs1) :
    ∀ (xs2 ys2 : List ℕ) (mid : ℕ) (rest : List ℕ),
    IsCarryChain g k xs2 ys2 (mid :: rest) →
    cs1.getLast? = some mid →
    IsCarryChain g k (xs1 ++ xs2) (ys1 ++ ys2) (cs1 ++ rest) := by
  induction h1 with
  | nil c =>
    intro xs2 ys2 mid rest h2 hlast
    simp only [List.getLast?_singleton] at hlast
    have heq : c = mid := Option.some_inj.mp hlast
    subst heq
    simpa using h2
  | cons x y c₀' c₁ xs ys cs hstep htail ih =>
    intro xs2 ys2 mid rest h2 hlast
    have hlast' : (c₁ :: cs).getLast? = some mid := by
      have hgg := chain_getLast_cons c₀' c₁ cs
      rw [← hgg]
      exact hlast
    have iht := ih xs2 ys2 mid rest h2 hlast'
    simp only [List.cons_append] at *
    exact IsCarryChain.cons x y c₀' c₁ (xs ++ xs2) (ys ++ ys2) (cs ++ rest) hstep iht

private def buildDigits (g k : ℕ) : List ℕ → ℕ → List ℕ
  | [], _ => []
  | x :: xs, c₀ => ((k * x + c₀) % g) :: buildDigits g k xs ((k * x + c₀) / g)

private def buildCarries (g k : ℕ) : List ℕ → ℕ → List ℕ
  | [], c₀ => [c₀]
  | x :: xs, c₀ => c₀ :: buildCarries g k xs ((k * x + c₀) / g)

private theorem buildCarries_form (g k : ℕ) (xs : List ℕ) (c : ℕ) :
    ∃ t, buildCarries g k xs c = c :: t := by
  cases xs with
  | nil => exact ⟨[], rfl⟩
  | cons y ys => exact ⟨buildCarries g k ys ((k * y + c) / g), rfl⟩

private theorem build_chain (g k : ℕ) (xs : List ℕ) (c₀ : ℕ) :
    IsCarryChain g k xs (buildDigits g k xs c₀) (buildCarries g k xs c₀) := by
  induction xs generalizing c₀ with
  | nil =>
    simp only [buildDigits, buildCarries]
    exact IsCarryChain.nil c₀
  | cons x xs ih =>
    have hstep : k * x + c₀ = (k * x + c₀) % g + ((k * x + c₀) / g) * g := by
      calc k * x + c₀
          = g * ((k * x + c₀) / g) + (k * x + c₀) % g := (Nat.div_add_mod _ _).symm
        _ = (k * x + c₀) % g + ((k * x + c₀) / g) * g := by ring
    simp only [buildDigits, buildCarries]
    obtain ⟨t, ht⟩ := buildCarries_form g k xs ((k * x + c₀) / g)
    have htail := ih ((k * x + c₀) / g)
    rw [ht] at htail ⊢
    exact IsCarryChain.cons x ((k * x + c₀) % g) c₀ ((k * x + c₀) / g) xs
      (buildDigits g k xs ((k * x + c₀) / g)) t hstep htail

private theorem buildCarries_all_lt (g k : ℕ)
    (xs : List ℕ) (c₀ : ℕ) (hc₀ : c₀ < k) (hx : ∀ x ∈ xs, x < g) :
    ∀ c ∈ buildCarries g k xs c₀, c < k := by
  induction xs generalizing c₀ with
  | nil =>
    simp only [buildCarries]
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact hc₀
  | cons x xs ih =>
    simp only [buildCarries]
    intro c hc
    simp only [List.mem_cons] at hc
    cases hc with
    | inl h => subst h; exact hc₀
    | inr h =>
      have hxhead : x < g := hx x (by simp)
      have hxtail : ∀ x' ∈ xs, x' < g := fun x' hx' => hx x' (by simp [hx'])
      have h1 : k * (x + 1) ≤ k * g := by
        apply Nat.mul_le_mul_left
        exact hxhead
      have h2 : k * x + c₀ < k * (x + 1) := by
        have e : k * (x + 1) = k * x + k := by ring
        omega
      have hlt : k * x + c₀ < k * g := lt_of_lt_of_le h2 h1
      have hlt' : k * x + c₀ < g * k := by
        rw [Nat.mul_comm g k]
        exact hlt
      have hbound : (k * x + c₀) / g < k := Nat.div_lt_of_lt_mul hlt'
      exact ih ((k * x + c₀) / g) hbound hxtail c h

private theorem build_match (g k : ℕ) (hg : 0 < g)
    (xs : List ℕ) (c₀ : ℕ) :
    ∀ (ys : List ℕ) (cN : ℕ),
    (∀ y ∈ ys, y < g) → xs.length = ys.length →
    k * Nat.ofDigits g xs + c₀ = Nat.ofDigits g ys + cN * g ^ xs.length →
    buildDigits g k xs c₀ = ys ∧ (buildCarries g k xs c₀).getLast? = some cN := by
  induction xs generalizing c₀ with
  | nil =>
    intro ys cN hy hlen hbal
    cases ys with
    | nil =>
      have hc : c₀ = cN := by simpa using hbal
      subst hc
      simp [buildDigits, buildCarries]
    | cons y ys' =>
      simp only [List.length_nil, List.length_cons] at hlen
      omega
  | cons x xs ih =>
    intro ys cN hy hlen hbal
    cases ys with
    | nil =>
      simp only [List.length_cons, List.length_nil] at hlen
      omega
    | cons y ys' =>
      simp only [List.length_cons] at hlen
      have hlen' : xs.length = ys'.length := by omega
      simp only [Nat.ofDigits_cons, List.length_cons] at hbal
      have hyhead : y < g := hy y (by simp)
      have hytail : ∀ y' ∈ ys', y' < g := fun y' hy' => hy y' (by simp [hy'])
      have hmod_lhs :
          (k * (x + g * Nat.ofDigits g xs) + c₀) % g
            = (k * x + c₀) % g := by
        have e : k * (x + g * Nat.ofDigits g xs) + c₀
            = (k * x + c₀) + g * (k * Nat.ofDigits g xs) := by ring
        rw [e, Nat.add_mul_mod_self_left]
      have hmod_rhs : (y + g * Nat.ofDigits g ys' + cN * g ^ (xs.length + 1)) % g = y := by
        have e : y + g * Nat.ofDigits g ys' + cN * g ^ (xs.length + 1)
            = y + g * (Nat.ofDigits g ys' + cN * g ^ xs.length) := by
          rw [pow_succ]; ring
        rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hyhead]
      have h : (k * (x + g * Nat.ofDigits g xs) + c₀) % g
          = (y + g * Nat.ofDigits g ys' + cN * g ^ (xs.length + 1)) % g := by rw [hbal]
      rw [hmod_lhs, hmod_rhs] at h
      have hhead : (k * x + c₀) % g = y := h
      have hq : k * x + c₀ = y + ((k * x + c₀) / g) * g := by
        have hdiv := Nat.div_add_mod (k * x + c₀) g
        rw [hhead] at hdiv
        have hcomm : ((k * x + c₀) / g) * g = g * ((k * x + c₀) / g) := Nat.mul_comm _ _
        omega
      set q := (k * x + c₀) / g with hqdef
      have eL : k * (x + g * Nat.ofDigits g xs) + c₀
          = (y + q * g) + g * (k * Nat.ofDigits g xs) := by rw [← hq]; ring
      have eR : y + g * Nat.ofDigits g ys' + cN * g ^ (xs.length + 1)
          = y + g * (Nat.ofDigits g ys' + cN * g ^ xs.length) := by
        rw [pow_succ]; ring
      rw [eL, eR] at hbal
      rw [Nat.add_assoc] at hbal
      have hcancel : q * g + g * (k * Nat.ofDigits g xs)
          = g * (Nat.ofDigits g ys' + cN * g ^ xs.length) :=
        Nat.add_left_cancel hbal
      have hfactor : g * (q + k * Nat.ofDigits g xs)
          = g * (Nat.ofDigits g ys' + cN * g ^ xs.length) := by
        have hc1 : q * g = g * q := Nat.mul_comm _ _
        rw [hc1, ← Nat.mul_add] at hcancel
        exact hcancel
      have htail_bal : k * Nat.ofDigits g xs + q
          = Nat.ofDigits g ys' + cN * g ^ xs.length := by
        have hcc : q + k * Nat.ofDigits g xs
            = Nat.ofDigits g ys' + cN * g ^ xs.length :=
          mul_left_cancel₀ (ne_of_gt hg) hfactor
        omega
      have ih' := ih q ys' cN hytail hlen' htail_bal
      obtain ⟨ih1, ih2⟩ := ih'
      constructor
      · simp only [buildDigits]
        rw [hhead, ih1]
      · simp only [buildCarries]
        obtain ⟨t, ht⟩ := buildCarries_form g k xs q
        have hlast_eq : (c₀ :: buildCarries g k xs q).getLast?
            = (buildCarries g k xs q).getLast? := by
          rw [ht]
          exact chain_getLast_cons c₀ q t
        rw [hlast_eq, ht] at ⊢
        rw [ht] at ih2
        exact ih2

private theorem chain_len (g k : ℕ) (xs ys cs : List ℕ) (h : IsCarryChain g k xs ys cs) :
    xs.length = ys.length ∧ cs.length = xs.length + 1 := by
  induction h with
  | nil c => simp
  | cons x y c₀ c₁ xs ys cs hstep htail ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · simp [h1]
    · simp [h2]

private theorem chain_take (g k : ℕ) (m : ℕ) : ∀ (xs ys cs : List ℕ),
    IsCarryChain g k xs ys cs → IsCarryChain g k (xs.take m) (ys.take m) (cs.take (m+1)) := by
  induction m with
  | zero =>
    intro xs ys cs h
    cases h with
    | nil c =>
      simp only [List.take_zero]
      exact IsCarryChain.nil c
    | cons x y c₀ c₁ xs ys cs hstep htail =>
      simp only [List.take_zero]
      exact IsCarryChain.nil c₀
  | succ m ih =>
    intro xs ys cs h
    cases h with
    | nil c =>
      simp only [List.take_nil, List.take_succ_cons]
      exact IsCarryChain.nil c
    | cons x y c₀ c₁ xs ys cs hstep htail =>
      simp only [List.take_succ_cons]
      have htail' := ih xs ys (c₁ :: cs) htail
      exact IsCarryChain.cons x y c₀ c₁ (xs.take m) (ys.take m) _ hstep htail'

private theorem chain_drop (g k : ℕ) (m : ℕ) : ∀ (xs ys cs : List ℕ),
    (h : IsCarryChain g k xs ys cs) → m ≤ xs.length →
    IsCarryChain g k (xs.drop m) (ys.drop m) (cs.drop m) := by
  induction m with
  | zero => intro xs ys cs h _; simpa using h
  | succ m ih =>
    intro xs ys cs h hm
    cases h with
    | nil c =>
      simp only [List.length_nil] at hm
      omega
    | cons x y c₀ c₁ xs ys cs hstep htail =>
      simp only [List.drop_succ_cons]
      have hlen : m ≤ xs.length := by
        simp only [List.length_cons] at hm ⊢
        omega
      exact ih xs ys (c₁ :: cs) htail hlen

private theorem chain_head2 (g k : ℕ) (x : ℕ) (xs : List ℕ) (y : ℕ) (ys : List ℕ) (c₀ : ℕ)
    (rest : List ℕ)
    (h : IsCarryChain g k (x :: xs) (y :: ys) (c₀ :: rest)) :
    ∃ c₁ cs, rest = c₁ :: cs ∧ k * x + c₀ = y + c₁ * g ∧ IsCarryChain g k xs ys (c₁ :: cs) := by
  cases h with
  | cons x' y' d₀ d₁ xs' ys' cs' hstep htail =>
    exact ⟨d₁, cs', rfl, hstep, htail⟩

private theorem chain_step_at (g k : ℕ) (xs ys cs : List ℕ) (h : IsCarryChain g k xs ys cs)
    (i : ℕ) (hi : i < xs.length) :
    k * xs[i] + cs[i]'(by obtain ⟨h1,h2⟩ := chain_len g k xs ys cs h; omega) =
      ys[i]'(by obtain ⟨h1,h2⟩ := chain_len g k xs ys cs h; omega) +
        cs[i+1]'(by obtain ⟨h1,h2⟩ := chain_len g k xs ys cs h; omega) * g := by
  have hlen := chain_len g k xs ys cs h
  obtain ⟨hxy, hcs⟩ := hlen
  have hi_le : i ≤ xs.length := Nat.le_of_lt hi
  have hdrop := chain_drop g k i xs ys cs h hi_le
  have hne_x : xs.drop i ≠ [] := by
    rw [ne_eq, List.drop_eq_nil_iff]
    omega
  have hne_y : ys.drop i ≠ [] := by
    rw [ne_eq, List.drop_eq_nil_iff]
    omega
  have hne_c : cs.drop i ≠ [] := by
    rw [ne_eq, List.drop_eq_nil_iff]
    omega
  obtain ⟨x', xs', hdx⟩ := List.exists_cons_of_ne_nil hne_x
  obtain ⟨y', ys', hdy⟩ := List.exists_cons_of_ne_nil hne_y
  obtain ⟨c0', crest, hdc0⟩ := List.exists_cons_of_ne_nil hne_c
  have hcrest_ne : crest ≠ [] := by
    have h1 : 1 < (cs.drop i).length := by rw [List.length_drop]; omega
    rw [hdc0] at h1
    simp at h1
    exact List.ne_nil_of_length_pos (by omega)
  obtain ⟨c1', cs', hdc1⟩ := List.exists_cons_of_ne_nil hcrest_ne
  have hdc : cs.drop i = c0' :: c1' :: cs' := by rw [hdc0, hdc1]
  rw [hdx, hdy, hdc] at hdrop
  obtain ⟨c1b, csb, heq, hstep, _⟩ := chain_head2 g k x' xs' y' ys' c0' (c1' :: cs') hdrop
  have heq1 : c1' = c1b := by simpa using congrArg List.head? heq
  have heq2 : cs' = csb := by
    have htail_eq : (c1' :: cs').tail = (c1b :: csb).tail := by rw [heq]
    simpa using htail_eq
  subst heq1
  subst heq2
  have hx' : x' = xs[i] := by
    have hh := List.head_drop (l := xs) (i := i) hne_x
    simp only [hdx, List.head_cons] at hh
    exact hh
  have hy' : y' = ys[i]'(by omega) := by
    have hh := List.head_drop (l := ys) (i := i) hne_y
    simp only [hdy, List.head_cons] at hh
    exact hh
  have hc0' : c0' = cs[i]'(by omega) := by
    have hh := List.head_drop (l := cs) (i := i) hne_c
    simp only [hdc, List.head_cons] at hh
    exact hh
  have hc1' : c1' = cs[i+1]'(by omega) := by
    have hne_c1 : cs.drop (i+1) ≠ [] := by
      rw [ne_eq, List.drop_eq_nil_iff]
      omega
    have hh := List.head_drop (l := cs) (i := i+1) hne_c1
    have hdrop_succ : cs.drop (i+1) = c1' :: cs' := by
      have hdd := @List.drop_drop ℕ 1 i cs
      have h1 : cs.drop (i+1) = (cs.drop i).drop 1 := by
        rw [← hdd]
      rw [h1, hdc]
      simp only [List.drop_one, List.tail_cons]
    simp only [hdrop_succ, List.head_cons] at hh
    exact hh
  rw [hx', hy', hc0', hc1'] at hstep
  exact hstep

private def labelsOf (D : List ℕ) : List (ℕ × ℕ) :=
  List.zip (D.take (D.length / 2)) (D.reverse.take (D.length / 2))

private def carriesOf (g k : ℕ) (D : List ℕ) : List ℕ :=
  buildCarries g k D.reverse 0

private def nodesOf (g k : ℕ) (D : List ℕ) : List (ℕ × ℕ) :=
  List.zip ((carriesOf g k D).reverse.take (D.length / 2 + 1))
    ((carriesOf g k D).take (D.length / 2 + 1))

private theorem labelsOf_length (D : List ℕ) :
    (labelsOf D).length = D.length / 2 := by
  unfold labelsOf
  rw [List.length_zip]
  have h1 : (D.take (D.length / 2)).length = D.length / 2 :=
    List.length_take_of_le (Nat.div_le_self _ _)
  have hle : D.length / 2 ≤ D.reverse.length := by
    rw [List.length_reverse]
    exact Nat.div_le_self _ _
  have h2 : (D.reverse.take (D.length / 2)).length = D.length / 2 :=
    List.length_take_of_le hle
  omega

private theorem carriesOf_form (g k : ℕ) (D : List ℕ) :
    ∃ t, carriesOf g k D = 0 :: t := by
  unfold carriesOf
  obtain ⟨t, ht⟩ := buildCarries_form g k D.reverse 0
  exact ⟨t, ht⟩

private theorem carriesOf_length (g k : ℕ) (D : List ℕ) :
    (carriesOf g k D).length = D.length + 1 := by
  unfold carriesOf
  have h := (chain_len g k D.reverse (buildDigits g k D.reverse 0)
    (buildCarries g k D.reverse 0) (build_chain g k D.reverse 0)).2
  simp [List.length_reverse] at h ⊢
  omega

private theorem nodesOf_length (g k : ℕ) (D : List ℕ) :
    (nodesOf g k D).length = D.length / 2 + 1 := by
  unfold nodesOf
  rw [List.length_zip]
  have hcl := carriesOf_length g k D
  have h1 : ((carriesOf g k D).take (D.length / 2 + 1)).length = D.length / 2 + 1 := by
    apply List.length_take_of_le
    omega
  have hle : D.length / 2 + 1 ≤ (carriesOf g k D).reverse.length := by
    rw [List.length_reverse]
    omega
  have h2 : ((carriesOf g k D).reverse.take (D.length / 2 + 1)).length
      = D.length / 2 + 1 :=
    List.length_take_of_le hle
  omega

private theorem revMult_len_ge_two (D : List ℕ)
    (h : (∃ first middle last, D = first :: middle ++ [last] ∧ first ≠ 0 ∧ last ≠ 0)) :
    2 ≤ D.length := by
  obtain ⟨first, middle, last, heq, _, _⟩ := h
  rw [heq]
  simp

private def reconEven (labels : List (ℕ × ℕ)) : List ℕ :=
  (labels.map Prod.fst) ++ (labels.map Prod.snd).reverse

private def reconOdd (labels : List (ℕ × ℕ)) (mid : ℕ) : List ℕ :=
  (labels.map Prod.fst) ++ [mid] ++ (labels.map Prod.snd).reverse

private theorem reconEven_length (labels : List (ℕ × ℕ)) :
    (reconEven labels).length = labels.length * 2 := by
  unfold reconEven
  simp [List.length_reverse]
  omega

private theorem reconOdd_length (labels : List (ℕ × ℕ)) (mid : ℕ) :
    (reconOdd labels mid).length = labels.length * 2 + 1 := by
  unfold reconOdd
  simp [List.length_reverse]
  omega

private theorem map_fst_labelsOf (D : List ℕ) :
    (labelsOf D).map Prod.fst = D.take (D.length / 2) := by
  unfold labelsOf
  have hle : (D.take (D.length / 2)).length ≤ (D.reverse.take (D.length / 2)).length := by
    have h1 : (D.take (D.length / 2)).length = D.length / 2 :=
      List.length_take_of_le (Nat.div_le_self _ _)
    have hle2 : D.length / 2 ≤ D.reverse.length := by
      rw [List.length_reverse]
      exact Nat.div_le_self _ _
    have h2 : (D.reverse.take (D.length / 2)).length = D.length / 2 :=
      List.length_take_of_le hle2
    omega
  exact List.map_fst_zip hle

private theorem map_snd_labelsOf (D : List ℕ) :
    (labelsOf D).map Prod.snd = D.reverse.take (D.length / 2) := by
  unfold labelsOf
  have hle : (D.reverse.take (D.length / 2)).length ≤ (D.take (D.length / 2)).length := by
    have h1 : (D.take (D.length / 2)).length = D.length / 2 :=
      List.length_take_of_le (Nat.div_le_self _ _)
    have hle2 : D.length / 2 ≤ D.reverse.length := by
      rw [List.length_reverse]
      exact Nat.div_le_self _ _
    have h2 : (D.reverse.take (D.length / 2)).length = D.length / 2 :=
      List.length_take_of_le hle2
    omega
  exact List.map_snd_zip hle

private theorem reconEven_labelsOf_even (D : List ℕ) (m : ℕ) (hm : D.length / 2 = m)
    (heven : 2 * m = D.length) :
    reconEven (labelsOf D) = D := by
  have hfst := map_fst_labelsOf D
  have hsnd := map_snd_labelsOf D
  unfold reconEven
  rw [hfst, hsnd, hm]
  have hrev : (D.reverse.take m).reverse = D.drop (D.length - m) := by
    rw [List.take_reverse]
    simp
  rw [hrev]
  have hm_eq : D.length - m = m := by omega
  rw [hm_eq]
  exact List.take_append_drop m D

private theorem reconOdd_labelsOf_odd (D : List ℕ) (m mid : ℕ) (hm : D.length / 2 = m)
    (hodd : m * 2 + 1 = D.length) (hmid : (D.drop m).head? = some mid) :
    reconOdd (labelsOf D) mid = D := by
  have hfst := map_fst_labelsOf D
  have hsnd := map_snd_labelsOf D
  unfold reconOdd
  rw [hfst, hsnd, hm]
  have hrev : (D.reverse.take m).reverse = D.drop (D.length - m) := by
    rw [List.take_reverse]
    simp
  rw [hrev]
  have hlen_eq : D.length - m = m + 1 := by omega
  rw [hlen_eq]
  have hdrop_eq : D.drop m = mid :: D.drop (m + 1) := by
    have hhead := hmid
    have hne : D.drop m ≠ [] := by
      rw [ne_eq, List.drop_eq_nil_iff]
      omega
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
    have hh : (D.drop m).head? = some x := by rw [hx]; rfl
    rw [hh] at hhead
    have hxmid : x = mid := Option.some_inj.mp hhead
    subst hxmid
    rw [hx]
    congr 1
    have hdd := @List.drop_drop ℕ 1 m D
    have h1 : D.drop (m + 1) = (D.drop m).drop 1 := by rw [← hdd]
    rw [h1, hx]
    simp
  have htake_drop : D.take m ++ [mid] ++ D.drop (m + 1) = D := by
    have h1 : D.take m ++ D.drop m = D := List.take_append_drop m D
    rw [hdrop_eq] at h1
    simpa using h1
  exact htake_drop

private theorem canon_of_revMult (g k : ℕ) (hg : 0 < g)
    (hk0 : 0 < k) (D : List ℕ) (hdig : ∀ d ∈ D, d < g)
    (hbal : k * D.foldl (fun v d => v * g + d) 0
      = D.reverse.foldl (fun v d => v * g + d) 0) :
    buildDigits g k D.reverse 0 = D ∧
      (buildCarries g k D.reverse 0).getLast? = some 0 ∧
      (∀ c ∈ buildCarries g k D.reverse 0, c < k) ∧
      IsCarryChain g k D.reverse D
        (buildCarries g k D.reverse 0) := by
  have h1 := digitValue_eq g D
  have h2 := digitValue_eq g D.reverse
  rw [h1, h2, List.reverse_reverse] at hbal
  have hbal' : k * Nat.ofDigits g D.reverse + 0
      = Nat.ofDigits g D + 0 * g ^ D.reverse.length := by
    simp only [Nat.add_zero, Nat.zero_mul]
    exact hbal
  have hdig_rev : ∀ x ∈ D.reverse, x < g := by
    intro x hx
    exact hdig x (List.mem_reverse.mp hx)
  have hall := buildCarries_all_lt g k D.reverse 0 hk0 hdig_rev
  have hlen : D.reverse.length = D.length := List.length_reverse
  have hmatch := build_match g k hg D.reverse 0 D 0 hdig hlen hbal'
  obtain ⟨hdig_eq, hlast⟩ := hmatch
  have hchain := build_chain g k D.reverse 0
  rw [hdig_eq] at hchain
  exact ⟨hdig_eq, hlast, hall, hchain⟩

private theorem labelsOf_get (D : List ℕ) (i : ℕ)
    (hi : i < D.length / 2) :
    (labelsOf D)[i]'(by rw [labelsOf_length]; exact hi)
      = (D[i]'(by
          have hle : D.length / 2 ≤ D.length :=
            Nat.div_le_self D.length 2
          omega),
        D.reverse[i]'(by
          have hle : D.length / 2 ≤ D.reverse.length := by
            rw [List.length_reverse]
            exact Nat.div_le_self D.length 2
          omega)) := by
  unfold labelsOf
  rw [List.getElem_zip, List.getElem_take, List.getElem_take]

private theorem nodesOf_get (g k : ℕ) (D : List ℕ) (i : ℕ)
    (hi : i < D.length / 2 + 1) :
    (nodesOf g k D)[i]'(by rw [nodesOf_length]; exact hi)
      = ((carriesOf g k D).reverse[i]'(by
          have hcl := carriesOf_length g k D
          have hle : D.length / 2 + 1
              ≤ (carriesOf g k D).reverse.length := by
            rw [List.length_reverse]
            omega
          omega),
        (carriesOf g k D)[i]'(by
          have hcl := carriesOf_length g k D
          omega)) := by
  unfold nodesOf
  rw [List.getElem_zip, List.getElem_take, List.getElem_take]

private theorem labelsOf_mem_lt (g : ℕ) (D : List ℕ)
    (hdig : ∀ d ∈ D, d < g) (label : ℕ × ℕ)
    (hmem : label ∈ labelsOf D) :
    label.1 < g ∧ label.2 < g := by
  cases label with
  | mk a b =>
    unfold labelsOf at hmem
    obtain ⟨ha, hb⟩ := List.of_mem_zip hmem
    have haD : a ∈ D := List.mem_of_mem_take ha
    have hbR : b ∈ D.reverse := List.mem_of_mem_take hb
    have hbD : b ∈ D := List.mem_reverse.mp hbR
    exact ⟨hdig a haD, hdig b hbD⟩

private theorem nodesOf_mem_lt (g k : ℕ) (D : List ℕ)
    (hcar : ∀ c ∈ carriesOf g k D, c < k) (node : ℕ × ℕ)
    (hmem : node ∈ nodesOf g k D) :
    node.1 < k ∧ node.2 < k := by
  cases node with
  | mk a b =>
    unfold nodesOf at hmem
    obtain ⟨ha, hb⟩ := List.of_mem_zip hmem
    have haR : a ∈ (carriesOf g k D).reverse :=
      List.mem_of_mem_take ha
    have haC : a ∈ carriesOf g k D := List.mem_reverse.mp haR
    have hbC : b ∈ carriesOf g k D := List.mem_of_mem_take hb
    exact ⟨hcar a haC, hcar b hbC⟩

private theorem nodesOf_head (g k : ℕ) (D : List ℕ)
    (hlast : (carriesOf g k D).getLast? = some 0) :
    (nodesOf g k D).head? = some (0, 0) := by
  have hC0 : (carriesOf g k D).head? = some 0 := by
    obtain ⟨t, ht⟩ := carriesOf_form g k D
    rw [ht]
    rfl
  have hR0 : (carriesOf g k D).reverse.head? = some 0 := by
    rw [List.head?_reverse, hlast]
  have hne : D.length / 2 + 1 ≠ 0 := by omega
  have hAt : ((carriesOf g k D).reverse.take
      (D.length / 2 + 1)).head? = some 0 := by
    rw [List.head?_take, ite_eq_right hne, hR0]
  have hBt : ((carriesOf g k D).take
      (D.length / 2 + 1)).head? = some 0 := by
    rw [List.head?_take, ite_eq_right hne, hC0]
  obtain ⟨Arest, ha⟩ := List.head?_eq_some_iff.mp hAt
  obtain ⟨Brest, hb⟩ := List.head?_eq_some_iff.mp hBt
  unfold nodesOf
  rw [ha, hb, List.zip_cons_cons]
  rfl

private theorem labelsOf_first_nonzero (D : List ℕ)
    (hex : ∃ first middle last,
      D = first :: middle ++ [last] ∧ first ≠ 0 ∧ last ≠ 0) :
    ∃ first rest,
      labelsOf D = first :: rest ∧ first.1 ≠ 0 ∧ first.2 ≠ 0 := by
  obtain ⟨firstD, middle, last, heq, hfirst, hlast0⟩ := hex
  have hDhead : D.head? = some firstD := by
    rw [heq]
    rfl
  have heq2 : D = (firstD :: middle) ++ [last] := by
    rw [heq, List.cons_append]
  have hDlast : D.getLast? = some last := by
    rw [heq2, List.getLast?_append_cons,
      List.getLast?_singleton]
  have hRhead : D.reverse.head? = some last := by
    rw [List.head?_reverse, hDlast]
  have hlen2 := revMult_len_ge_two D
    ⟨firstD, middle, last, heq, hfirst, hlast0⟩
  have hmpos : D.length / 2 ≠ 0 := by omega
  have hAt : (D.take (D.length / 2)).head?
      = some firstD := by
    rw [List.head?_take, ite_eq_right hmpos, hDhead]
  have hBt : (D.reverse.take (D.length / 2)).head?
      = some last := by
    rw [List.head?_take, ite_eq_right hmpos, hRhead]
  obtain ⟨Arest, ha⟩ := List.head?_eq_some_iff.mp hAt
  obtain ⟨Brest, hb⟩ := List.head?_eq_some_iff.mp hBt
  unfold labelsOf
  rw [ha, hb, List.zip_cons_cons]
  exact ⟨(firstD, last), _, rfl, hfirst, hlast0⟩

private theorem rev_get_high (D : List ℕ) (i : ℕ)
    (hi : i < D.length) :
    D.reverse[D.length - 1 - i]'(by
        rw [List.length_reverse]
        omega) = D[i]'hi := by
  have hidx : D.length - 1 - (D.length - 1 - i) = i := by omega
  have h := List.getElem_reverse (l := D)
    (i := D.length - 1 - i)
    (h := by rw [List.length_reverse]; omega)
  simp only [hidx] at h
  exact h

private theorem fwd_forall2 (g k : ℕ) (D : List ℕ)
    (hchain : IsCarryChain g k D.reverse D (carriesOf g k D))
    (_hlen2 : 2 ≤ D.length) :
    List.Forall₂
      (fun label endpoints =>
        k * label.2 + endpoints.1.2 = label.1 + endpoints.2.2 * g ∧
        k * label.1 + endpoints.2.1 = label.2 + endpoints.1.1 * g)
      (labelsOf D)
      ((nodesOf g k D).zip (nodesOf g k D).tail) := by
  have hlab := labelsOf_length D
  have hnod := nodesOf_length g k D
  have htail : ((nodesOf g k D).tail).length = D.length / 2 := by
    rw [List.length_tail, hnod]
    omega
  have hzip : ((nodesOf g k D).zip
      (nodesOf g k D).tail).length = D.length / 2 := by
    rw [List.length_zip, hnod, htail]
    omega
  apply List.forall₂_of_length_eq_of_get ?_ ?_
  · rw [hlab, hzip]
  · intro i h1 h2
    have hi : i < D.length / 2 := by
      rw [hlab] at h1
      exact h1
    have hi1 : i < D.length / 2 + 1 := by omega
    have hi1' : i + 1 < D.length / 2 + 1 := by omega
    have hDle : D.length / 2 ≤ D.length := Nat.div_le_self _ _
    have hiD : i < D.length := by omega
    have hClen := carriesOf_length g k D
    have hiC : i < (carriesOf g k D).length := by omega
    have hiC1 : i + 1 < (carriesOf g k D).length := by omega
    have hiRC : i < (carriesOf g k D).reverse.length := by
      rw [List.length_reverse]
      omega
    have hiRC1 : i + 1
        < (carriesOf g k D).reverse.length := by
      rw [List.length_reverse]
      omega
    have hlab_eq := labelsOf_get D i hi
    have hnod_eq := nodesOf_get g k D i hi1
    have hnod_eq1 := nodesOf_get g k D (i + 1) hi1'
    have hzip_eq := List.getElem_zip (l := nodesOf g k D)
      (l' := (nodesOf g k D).tail) (i := i) (h := h2)
    have htail_eq := List.getElem_tail (l := nodesOf g k D)
      (i := i) (h := by rw [htail]; exact hi)
    have hlow := chain_step_at g k D.reverse D
      (carriesOf g k D) hchain i
      (by rw [List.length_reverse]; exact hiD)
    have hjD : D.length - 1 - i < D.length := by omega
    have hhigh := chain_step_at g k D.reverse D
      (carriesOf g k D) hchain (D.length - 1 - i)
      (by rw [List.length_reverse]; exact hjD)
    have hrevi := List.getElem_reverse (l := D)
      (i := i) (h := by rw [List.length_reverse]; omega)
    have hrevj := rev_get_high D i hiD
    have hrevCi := List.getElem_reverse
      (l := carriesOf g k D) (i := i) (h := hiRC)
    have hidxCi : (carriesOf g k D).length - 1 - i
        = D.length - i := by omega
    simp only [hidxCi] at hrevCi
    have hrevCi1 := List.getElem_reverse
      (l := carriesOf g k D) (i := i + 1) (h := hiRC1)
    have hidxCi1 : (carriesOf g k D).length - 1 - (i + 1)
        = D.length - (i + 1) := by omega
    simp only [hidxCi1] at hrevCi1
    have hCj : (carriesOf g k D)[D.length - 1 - i]'(by omega)
        = (carriesOf g k D)[D.length - (i + 1)]'(by omega) := by
      have hidx : D.length - 1 - i = D.length - (i + 1) := by omega
      simp only [hidx]
    have hCj1 : (carriesOf g k D)[D.length - 1 - i + 1]'(by omega)
        = (carriesOf g k D)[D.length - i]'(by omega) := by
      have hidx : D.length - 1 - i + 1 = D.length - i := by omega
      simp only [hidx]
    simp only [hrevj, hCj, hCj1] at hhigh
    simp only [hrevi] at hlow
    have hL1 : ((labelsOf D).get ⟨i, h1⟩).1
        = D[i]'hiD := by
      have h := congrArg Prod.fst hlab_eq
      simp only at h
      exact h
    have hL2 : ((labelsOf D).get ⟨i, h1⟩).2
        = D[D.length - 1 - i]'hjD := by
      have h := congrArg Prod.snd hlab_eq
      simp only [hrevi] at h
      exact h
    have hS2 : ((((nodesOf g k D).zip
        (nodesOf g k D).tail).get ⟨i, h2⟩).1).2
        = (carriesOf g k D)[i]'hiC := by
      have hz := congrArg Prod.fst hzip_eq
      simp only [hnod_eq] at hz
      have h := congrArg Prod.snd hz
      simp only at h
      exact h
    have hT2 : ((((nodesOf g k D).zip
        (nodesOf g k D).tail).get ⟨i, h2⟩).2).2
        = (carriesOf g k D)[i + 1]'hiC1 := by
      have hz := congrArg Prod.snd hzip_eq
      simp only [htail_eq, hnod_eq1] at hz
      have h := congrArg Prod.snd hz
      simp only at h
      exact h
    have hS1 : ((((nodesOf g k D).zip
        (nodesOf g k D).tail).get ⟨i, h2⟩).1).1
        = (carriesOf g k D)[D.length - i]'
          (by omega) := by
      have hz := congrArg Prod.fst hzip_eq
      simp only [hnod_eq, hrevCi] at hz
      have h := congrArg Prod.fst hz
      simp only at h
      exact h
    have hT1 : ((((nodesOf g k D).zip
        (nodesOf g k D).tail).get ⟨i, h2⟩).2).1
        = (carriesOf g k D)[D.length - (i + 1)]'
          (by omega) := by
      have hz := congrArg Prod.snd hzip_eq
      simp only [htail_eq, hnod_eq1, hrevCi1] at hz
      have h := congrArg Prod.fst hz
      simp only at h
      exact h
    rw [hL1, hL2, hS2, hT2, hS1, hT1]
    exact ⟨hlow, hhigh⟩

private theorem fwd_pivot_even (g k : ℕ) (D : List ℕ)
    (heven : Even D.length) :
    ∃ r, (nodesOf g k D).getLast? = some (r, r) := by
  have h2m := Nat.two_mul_div_two_of_even heven
  have hnod := nodesOf_length g k D
  have hne : nodesOf g k D ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hnod]; omega)
  have hlast := List.getLast?_eq_getLast_of_ne_nil hne
  have hget := List.getLast_eq_getElem hne
  have hlen1 : (nodesOf g k D).length - 1
      = D.length / 2 := by
    rw [hnod]
    omega
  have hidx : (nodesOf g k D)[(nodesOf g k D).length - 1]'
      (by omega) = (nodesOf g k D)[D.length / 2]'
      (by rw [hnod]; omega) := by
    simp only [hlen1]
  have hm : D.length / 2 < D.length / 2 + 1 := by omega
  have hnod_m := nodesOf_get g k D (D.length / 2) hm
  have hrev := List.getElem_reverse (l := carriesOf g k D)
    (i := D.length / 2)
    (h := by
      rw [List.length_reverse]
      have hcl := carriesOf_length g k D
      omega)
  have hcl := carriesOf_length g k D
  have hidx2 : (carriesOf g k D).length - 1 - D.length / 2
      = D.length / 2 := by omega
  simp only [hidx2] at hrev
  have hnod_eq : (nodesOf g k D)[D.length / 2]'(by
      rw [hnod]
      omega)
      = ((carriesOf g k D)[D.length / 2]'(by omega),
        (carriesOf g k D)[D.length / 2]'(by omega)) := by
    rw [hnod_m, hrev]
  rw [hlast, hget, hidx, hnod_eq]
  exact ⟨_, rfl⟩

private theorem fwd_pivot_odd (g k : ℕ) (D : List ℕ)
    (hchain : IsCarryChain g k D.reverse D (carriesOf g k D))
    (hdig : ∀ d ∈ D, d < g) (hodd : Odd D.length) :
    ∃ r s middle,
      (nodesOf g k D).getLast? = some (r, s) ∧ middle < g ∧
        (k * middle + s = middle + r * g ∧
          k * middle + s = middle + r * g) ∧
        (D.drop (D.length / 2)).head? = some middle := by
  have hodd_eq := Nat.div_two_mul_two_add_one_of_odd hodd
  have hnod := nodesOf_length g k D
  have hne : nodesOf g k D ≠ [] :=
    List.ne_nil_of_length_pos (by rw [hnod]; omega)
  have hlast := List.getLast?_eq_getLast_of_ne_nil hne
  have hget := List.getLast_eq_getElem hne
  have hlen1 : (nodesOf g k D).length - 1
      = D.length / 2 := by
    rw [hnod]
    omega
  have hidx : (nodesOf g k D)[(nodesOf g k D).length - 1]'
      (by omega) = (nodesOf g k D)[D.length / 2]'
      (by rw [hnod]; omega) := by
    simp only [hlen1]
  have hm : D.length / 2 < D.length / 2 + 1 := by omega
  have hnod_m := nodesOf_get g k D (D.length / 2) hm
  have hrev := List.getElem_reverse (l := carriesOf g k D)
    (i := D.length / 2)
    (h := by
      rw [List.length_reverse]
      have hcl := carriesOf_length g k D
      omega)
  have hcl := carriesOf_length g k D
  have hidx2 : (carriesOf g k D).length - 1 - D.length / 2
      = D.length / 2 + 1 := by omega
  simp only [hidx2] at hrev
  have hmD : D.length / 2 < D.length := by omega
  have hmid_lt : D[D.length / 2]'hmD < g :=
    hdig _ (List.getElem_mem hmD)
  have hdrop : (D.drop (D.length / 2)).head?
      = some (D[D.length / 2]'hmD) := by
    rw [List.head?_drop, List.getElem?_eq_getElem hmD]
  have hstep := chain_step_at g k D.reverse D
    (carriesOf g k D) hchain (D.length / 2)
    (by rw [List.length_reverse]; exact hmD)
  have hrev_mid := List.getElem_reverse (l := D)
    (i := D.length / 2)
    (h := by rw [List.length_reverse]; exact hmD)
  have hmid_idx : D.length - 1 - D.length / 2
      = D.length / 2 := by omega
  simp only [hmid_idx] at hrev_mid
  simp only [hrev_mid] at hstep
  have hnod_eq : (nodesOf g k D)[D.length / 2]'(by
      rw [hnod]
      omega)
      = ((carriesOf g k D)[D.length / 2 + 1]'(by omega),
        (carriesOf g k D)[D.length / 2]'(by omega)) := by
    rw [hnod_m, hrev]
  have hlast_eq : (nodesOf g k D).getLast?
      = some ((carriesOf g k D)[D.length / 2 + 1]'(by omega),
        (carriesOf g k D)[D.length / 2]'(by omega)) := by
    rw [hlast, hget, hidx, hnod_eq]
  refine ⟨_, _, _, hlast_eq, hmid_lt, ⟨hstep, hstep⟩, hdrop⟩

private theorem chain_singleton (g k x y c0 c1 : ℕ)
    (hstep : k * x + c0 = y + c1 * g) :
    IsCarryChain g k [x] [y] [c0, c1] :=
  IsCarryChain.cons x y c0 c1 [] [] [] hstep
    (IsCarryChain.nil c1)

private theorem chain_snoc (g k : ℕ) (xs ys cs : List ℕ)
    (h : IsCarryChain g k xs ys cs) (x y mid c' : ℕ)
    (hlast : cs.getLast? = some mid)
    (hstep : k * x + mid = y + c' * g) :
    IsCarryChain g k (xs ++ [x]) (ys ++ [y]) (cs ++ [c']) := by
  have h2 := chain_singleton g k x y mid c' hstep
  have happ := chain_append g k xs ys cs h [x] [y] mid [c'] h2
    hlast
  simpa using happ

private theorem low_chain_of_path (g k : ℕ)
    (L : List (ℕ × ℕ)) (N : List (ℕ × ℕ))
    (hlen : N.length = L.length + 1)
    (hforall : List.Forall₂
      (fun label endpoints =>
        k * label.2 + endpoints.1.2 = label.1 + endpoints.2.2 * g ∧
        k * label.1 + endpoints.2.1 = label.2 + endpoints.1.1 * g)
      L (N.zip N.tail)) :
    IsCarryChain g k (L.map Prod.snd) (L.map Prod.fst)
      (N.map Prod.snd) := by
  induction L generalizing N with
  | nil =>
    have hN1 : N.length = 1 := by
      simp only [List.length_nil] at hlen
      omega
    have hne : N ≠ [] := List.ne_nil_of_length_pos (by omega)
    obtain ⟨n0, Nrest, hN⟩ := List.exists_cons_of_ne_nil hne
    have hrest_nil : Nrest = [] := by
      have hlenN : N.length = Nrest.length + 1 := by
        rw [hN]
        simp only [List.length_cons]
      have hlen0 : Nrest.length = 0 := by omega
      exact List.length_eq_zero_iff.mp hlen0
    rw [hrest_nil] at hN
    simp only [List.map_nil] at ⊢
    rw [hN]
    simp only [List.map_cons, List.map_nil]
    exact IsCarryChain.nil _
  | cons a L' ih =>
    have hNlen : 2 ≤ N.length := by
      simp only [List.length_cons] at hlen
      omega
    have hne : N ≠ [] := List.ne_nil_of_length_pos (by omega)
    obtain ⟨n0, Nrest, hN⟩ := List.exists_cons_of_ne_nil hne
    have hNrest_ne : Nrest ≠ [] := by
      have hlenN : N.length = Nrest.length + 1 := by
        rw [hN]
        simp only [List.length_cons]
      exact List.ne_nil_of_length_pos (by omega)
    obtain ⟨n1, Nrest2, hNr⟩ := List.exists_cons_of_ne_nil hNrest_ne
    have hN2 : N = n0 :: n1 :: Nrest2 := by
      rw [hN, hNr]
    have htail_eq : N.tail = n1 :: Nrest2 := by
      rw [hN2]
      simp only [List.tail_cons]
    have hzip_eq : N.zip N.tail
        = (n0, n1) :: Nrest.zip Nrest.tail := by
      rw [hN, hNr]
      simp only [List.tail_cons, List.zip_cons_cons]
    rw [hzip_eq] at hforall
    cases hforall with
    | cons hhead htail =>
      have hlen_rest : Nrest.length = L'.length + 1 := by
        have hlenN : N.length = Nrest.length + 1 := by
          rw [hN]
          simp only [List.length_cons]
        simp only [List.length_cons] at hlen
        omega
      have htail_chain := ih Nrest hlen_rest htail
      have hstep := hhead.1
      have hmapL1 : (a :: L').map Prod.snd
          = a.2 :: L'.map Prod.snd := by
        simp only [List.map_cons]
      have hmapL2 : (a :: L').map Prod.fst
          = a.1 :: L'.map Prod.fst := by
        simp only [List.map_cons]
      have hmapN : N.map Prod.snd
          = n0.2 :: n1.2 :: (Nrest2.map Prod.snd) := by
        rw [hN2]
        simp only [List.map_cons]
      have hmapNr : Nrest.map Prod.snd
          = n1.2 :: Nrest2.map Prod.snd := by
        rw [hNr]
        simp only [List.map_cons]
      rw [hmapNr] at htail_chain
      rw [hmapL1, hmapL2, hmapN]
      exact IsCarryChain.cons a.2 a.1 n0.2 n1.2 _ _ _
        hstep htail_chain

private theorem high_chain_of_path (g k : ℕ)
    (L : List (ℕ × ℕ)) (N : List (ℕ × ℕ))
    (hlen : N.length = L.length + 1)
    (hforall : List.Forall₂
      (fun label endpoints =>
        k * label.2 + endpoints.1.2 = label.1 + endpoints.2.2 * g ∧
        k * label.1 + endpoints.2.1 = label.2 + endpoints.1.1 * g)
      L (N.zip N.tail)) :
    IsCarryChain g k (L.map Prod.fst).reverse
      (L.map Prod.snd).reverse (N.map Prod.fst).reverse := by
  induction L generalizing N with
  | nil =>
    have hN1 : N.length = 1 := by
      simp only [List.length_nil] at hlen
      omega
    have hne : N ≠ [] := List.ne_nil_of_length_pos (by omega)
    obtain ⟨n0, Nrest, hN⟩ := List.exists_cons_of_ne_nil hne
    have hlenN : N.length = Nrest.length + 1 := by
      rw [hN]
      simp only [List.length_cons]
    have hlen0 : Nrest.length = 0 := by omega
    have hrest_nil : Nrest = [] :=
      List.length_eq_zero_iff.mp hlen0
    rw [hrest_nil] at hN
    simp only [List.map_nil, List.reverse_nil] at ⊢
    rw [hN]
    simp only [List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil,
      List.nil_append]
    exact IsCarryChain.nil _
  | cons a L' ih =>
    have hne : N ≠ [] := List.ne_nil_of_length_pos (by
      simp only [List.length_cons] at hlen
      omega)
    obtain ⟨n0, Nrest, hN⟩ := List.exists_cons_of_ne_nil hne
    have hNrest_ne : Nrest ≠ [] := by
      have hlenN : N.length = Nrest.length + 1 := by
        rw [hN]
        simp only [List.length_cons]
      have h2 : 2 ≤ N.length := by
        simp only [List.length_cons] at hlen
        omega
      exact List.ne_nil_of_length_pos (by omega)
    obtain ⟨n1, Nrest2, hNr⟩ := List.exists_cons_of_ne_nil hNrest_ne
    have hzip_eq : N.zip N.tail
        = (n0, n1) :: Nrest.zip Nrest.tail := by
      rw [hN, hNr]
      simp only [List.tail_cons, List.zip_cons_cons]
    rw [hzip_eq] at hforall
    cases hforall with
    | cons hhead htail =>
      have hlen_rest : Nrest.length = L'.length + 1 := by
        have hlenN : N.length = Nrest.length + 1 := by
          rw [hN]
          simp only [List.length_cons]
        simp only [List.length_cons] at hlen
        omega
      have ih_chain := ih Nrest hlen_rest htail
      have hstep : k * a.1 + n1.1 = a.2 + n0.1 * g := hhead.2
      have hlast : (Nrest.map Prod.fst).reverse.getLast?
          = some n1.1 := by
        rw [List.getLast?_reverse]
        have hmap : Nrest.map Prod.fst
            = n1.1 :: Nrest2.map Prod.fst := by
          rw [hNr]
          simp only [List.map_cons]
        rw [hmap]
        rfl
      have hsnoc := chain_snoc g k (L'.map Prod.fst).reverse
        (L'.map Prod.snd).reverse (Nrest.map Prod.fst).reverse
        ih_chain a.1 a.2 n1.1 n0.1 hlast hstep
      have e1 : ((a :: L').map Prod.fst).reverse
          = (L'.map Prod.fst).reverse ++ [a.1] := by
        simp only [List.map_cons, List.reverse_cons]
      have e2 : ((a :: L').map Prod.snd).reverse
          = (L'.map Prod.snd).reverse ++ [a.2] := by
        simp only [List.map_cons, List.reverse_cons]
      have e3 : (N.map Prod.fst).reverse
          = (Nrest.map Prod.fst).reverse ++ [n0.1] := by
        have hmapN : N.map Prod.fst
            = n0.1 :: Nrest.map Prod.fst := by
          rw [hN]
          simp only [List.map_cons]
        rw [hmapN, List.reverse_cons]
      rw [e1, e2, e3]
      exact hsnoc

private theorem zip_map_roundtrip (L : List (ℕ × ℕ)) :
    List.zip (L.map Prod.fst) (L.map Prod.snd) = L := by
  have h := List.zip_unzip L
  simp only [List.unzip_fst, List.unzip_snd] at h
  exact h

private theorem reconEven_mem_lt (g : ℕ) (L : List (ℕ × ℕ))
    (hdig : ∀ l ∈ L, l.1 < g ∧ l.2 < g) (d : ℕ)
    (hmem : d ∈ reconEven L) : d < g := by
  unfold reconEven at hmem
  rw [List.mem_append] at hmem
  cases hmem with
  | inl h =>
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp h
    exact (hdig l hl).1
  | inr h =>
    have hmem2 : d ∈ L.map Prod.snd := List.mem_reverse.mp h
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hmem2
    exact (hdig l hl).2

private theorem reconOdd_mem_lt (g : ℕ) (L : List (ℕ × ℕ))
    (mid : ℕ) (hmid : mid < g)
    (hdig : ∀ l ∈ L, l.1 < g ∧ l.2 < g) (d : ℕ)
    (hmem : d ∈ reconOdd L mid) : d < g := by
  unfold reconOdd at hmem
  simp only [List.mem_append, List.mem_singleton] at hmem
  cases hmem with
  | inl h =>
    cases h with
    | inl hA =>
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hA
      exact (hdig l hl).1
    | inr hmid_eq =>
      rw [hmid_eq]
      exact hmid
  | inr hB =>
    have hmem2 : d ∈ L.map Prod.snd := List.mem_reverse.mp hB
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hmem2
    exact (hdig l hl).2

private theorem reconEven_nonzero (L : List (ℕ × ℕ))
    (hex : ∃ first rest,
      L = first :: rest ∧ first.1 ≠ 0 ∧ first.2 ≠ 0) :
    ∃ first middle last,
      reconEven L = first :: middle ++ [last] ∧
        first ≠ 0 ∧ last ≠ 0 := by
  obtain ⟨fl, rest, hL, h1, h2⟩ := hex
  have hA : L.map Prod.fst
      = fl.1 :: rest.map Prod.fst := by
    rw [hL]
    simp only [List.map_cons]
  have hB : L.map Prod.snd
      = fl.2 :: rest.map Prod.snd := by
    rw [hL]
    simp only [List.map_cons]
  have hBrev : (L.map Prod.snd).reverse
      = (rest.map Prod.snd).reverse ++ [fl.2] := by
    rw [hB, List.reverse_cons]
  unfold reconEven
  rw [hA, hBrev, List.cons_append, ← List.append_assoc]
  exact ⟨fl.1, _, fl.2, rfl, h1, h2⟩

private theorem reconOdd_nonzero (L : List (ℕ × ℕ)) (mid : ℕ)
    (hex : ∃ first rest,
      L = first :: rest ∧ first.1 ≠ 0 ∧ first.2 ≠ 0) :
    ∃ first middle last,
      reconOdd L mid = first :: middle ++ [last] ∧
        first ≠ 0 ∧ last ≠ 0 := by
  obtain ⟨fl, rest, hL, h1, h2⟩ := hex
  have hA : L.map Prod.fst
      = fl.1 :: rest.map Prod.fst := by
    rw [hL]
    simp only [List.map_cons]
  have hB : L.map Prod.snd
      = fl.2 :: rest.map Prod.snd := by
    rw [hL]
    simp only [List.map_cons]
  have hBrev : (L.map Prod.snd).reverse
      = (rest.map Prod.snd).reverse ++ [fl.2] := by
    rw [hB, List.reverse_cons]
  unfold reconOdd
  rw [hA, hBrev, List.cons_append, List.cons_append,
    ← List.append_assoc]
  exact ⟨fl.1, _, fl.2, rfl, h1, h2⟩

private theorem reconEven_reverse (L : List (ℕ × ℕ)) :
    (reconEven L).reverse
      = (L.map Prod.snd) ++ (L.map Prod.fst).reverse := by
  unfold reconEven
  rw [List.reverse_append, List.reverse_reverse]

private theorem reconOdd_reverse (L : List (ℕ × ℕ)) (mid : ℕ) :
    (reconOdd L mid).reverse
      = (L.map Prod.snd) ++ [mid] ++ (L.map Prod.fst).reverse := by
  unfold reconOdd
  rw [List.reverse_append, List.reverse_append,
    List.reverse_reverse, List.reverse_singleton,
    List.append_assoc]

private theorem reconEven_length_even (L : List (ℕ × ℕ)) :
    Even (reconEven L).length := by
  have hlen := reconEven_length L
  exact ⟨L.length, by rw [hlen]; ring⟩

private theorem reconOdd_length_odd (L : List (ℕ × ℕ))
    (mid : ℕ) : Odd (reconOdd L mid).length := by
  have hlen := reconOdd_length L mid
  exact ⟨L.length, by rw [hlen]; ring⟩

private theorem bwd_even_balance (g k : ℕ)
    (L N : List (ℕ × ℕ))
    (hlen : N.length = L.length + 1)
    (hhead : N.head? = some (0, 0))
    (hforall : List.Forall₂
      (fun label endpoints =>
        k * label.2 + endpoints.1.2 = label.1 + endpoints.2.2 * g ∧
        k * label.1 + endpoints.2.1 = label.2 + endpoints.1.1 * g)
      L (N.zip N.tail))
    (hpivot : ∃ r, N.getLast? = some (r, r))
    (hexL : ∃ first rest,
      L = first :: rest ∧ first.1 ≠ 0 ∧ first.2 ≠ 0) :
    k * (reconEven L).foldl (fun v d => v * g + d) 0
      = ((reconEven L).reverse).foldl
        (fun v d => v * g + d) 0 := by
  obtain ⟨r, hpiv⟩ := hpivot
  have hlow := low_chain_of_path g k L N hlen hforall
  have hhigh := high_chain_of_path g k L N hlen hforall
  have hlast_low : (N.map Prod.snd).getLast? = some r := by
    rw [List.getLast?_map, hpiv]
    rfl
  have hhead_high : ((N.map Prod.fst).reverse).head?
      = some r := by
    rw [List.head?_reverse, List.getLast?_map, hpiv]
    rfl
  obtain ⟨hrest, hhigh_cons⟩ :=
    List.head?_eq_some_iff.mp hhead_high
  have hLpos : 0 < L.length := by
    obtain ⟨fl, rest, hL, _, _⟩ := hexL
    rw [hL]
    simp only [List.length_cons, Nat.zero_lt_succ]
  have hhigh_len : ((N.map Prod.fst).reverse).length
      = L.length + 1 := by
    rw [List.length_reverse, List.length_map, hlen]
  have hrest_ne : hrest ≠ [] := by
    have hlen_hr : hrest.length + 1
        = ((N.map Prod.fst).reverse).length := by
      rw [hhigh_cons]
      simp only [List.length_cons]
    rw [hhigh_len] at hlen_hr
    exact List.ne_nil_of_length_pos (by omega)
  have hhigh_rw : IsCarryChain g k
      ((L.map Prod.fst).reverse) ((L.map Prod.snd).reverse)
      (r :: hrest) := hhigh_cons ▸ hhigh
  have hfull := chain_append g k (L.map Prod.snd)
    (L.map Prod.fst) (N.map Prod.snd) hlow
    ((L.map Prod.fst).reverse) ((L.map Prod.snd).reverse)
    r hrest hhigh_rw hlast_low
  have hhead_low : (N.map Prod.snd).head? = some 0 := by
    rw [List.head?_map, hhead]
    rfl
  obtain ⟨cs1rest, hcs1⟩ :=
    List.head?_eq_some_iff.mp hhead_low
  have hfull_cs : (N.map Prod.snd) ++ hrest
      = 0 :: (cs1rest ++ hrest) := by
    rw [hcs1, List.cons_append]
  have hlast_high : ((N.map Prod.fst).reverse).getLast?
      = some 0 := by
    rw [List.getLast?_reverse, List.head?_map, hhead]
    rfl
  have hrest_last : hrest.getLast? = some 0 := by
    have h1 : ((N.map Prod.fst).reverse).getLast?
        = hrest.getLast? := by
      rw [hhigh_cons]
      exact List.getLast?_cons_of_ne_nil hrest_ne
    rw [hlast_high] at h1
    exact h1.symm
  have hfull_last : ((N.map Prod.snd) ++ hrest).getLast?
      = some 0 := by
    rw [List.getLast?_append_of_ne_nil _ hrest_ne]
    exact hrest_last
  have hbal := chain_balance g k ((L.map Prod.snd)
      ++ (L.map Prod.fst).reverse)
    ((L.map Prod.fst) ++ (L.map Prod.snd).reverse)
    ((N.map Prod.snd) ++ hrest) hfull 0 hfull_last 0
    (cs1rest ++ hrest) hfull_cs
  have hxs_eq : (L.map Prod.snd) ++ (L.map Prod.fst).reverse
      = (reconEven L).reverse := by
    rw [reconEven_reverse L]
  have hys_eq : (L.map Prod.fst) ++ (L.map Prod.snd).reverse
      = reconEven L := rfl
  rw [hxs_eq, hys_eq] at hbal
  have hbal_simple : k * Nat.ofDigits g (reconEven L).reverse
      = Nat.ofDigits g (reconEven L) := by
    simp only [Nat.add_zero, Nat.zero_mul] at hbal
    exact hbal
  have h1 := digitValue_eq g (reconEven L)
  have h2 := digitValue_eq g (reconEven L).reverse
  rw [h1, h2, List.reverse_reverse]
  exact hbal_simple

private theorem bwd_odd_balance (g k : ℕ)
    (L N : List (ℕ × ℕ)) (mid r s : ℕ)
    (hlen : N.length = L.length + 1)
    (hhead : N.head? = some (0, 0))
    (hforall : List.Forall₂
      (fun label endpoints =>
        k * label.2 + endpoints.1.2 = label.1 + endpoints.2.2 * g ∧
        k * label.1 + endpoints.2.1 = label.2 + endpoints.1.1 * g)
      L (N.zip N.tail))
    (hpiv_last : N.getLast? = some (r, s))
    (hpiv_mid : k * mid + s = mid + r * g)
    (hexL : ∃ first rest,
      L = first :: rest ∧ first.1 ≠ 0 ∧ first.2 ≠ 0) :
    k * (reconOdd L mid).foldl (fun v d => v * g + d) 0
      = ((reconOdd L mid).reverse).foldl
        (fun v d => v * g + d) 0 := by
  have hlow := low_chain_of_path g k L N hlen hforall
  have hhigh := high_chain_of_path g k L N hlen hforall
  have hmid_chain := chain_singleton g k mid mid s r hpiv_mid
  have hlast_low : (N.map Prod.snd).getLast? = some s := by
    rw [List.getLast?_map, hpiv_last]
    rfl
  have hlow_mid := chain_append g k (L.map Prod.snd)
    (L.map Prod.fst) (N.map Prod.snd) hlow [mid] [mid]
    s [r] hmid_chain hlast_low
  have hhead_high : ((N.map Prod.fst).reverse).head?
      = some r := by
    rw [List.head?_reverse, List.getLast?_map, hpiv_last]
    rfl
  obtain ⟨hrest, hhigh_cons⟩ :=
    List.head?_eq_some_iff.mp hhead_high
  have hLpos : 0 < L.length := by
    obtain ⟨fl, rest, hL, _, _⟩ := hexL
    rw [hL]
    simp only [List.length_cons, Nat.zero_lt_succ]
  have hhigh_len : ((N.map Prod.fst).reverse).length
      = L.length + 1 := by
    rw [List.length_reverse, List.length_map, hlen]
  have hrest_ne : hrest ≠ [] := by
    have hlen_hr : hrest.length + 1
        = ((N.map Prod.fst).reverse).length := by
      rw [hhigh_cons]
      simp only [List.length_cons]
    rw [hhigh_len] at hlen_hr
    exact List.ne_nil_of_length_pos (by omega)
  have hhigh_rw : IsCarryChain g k
      ((L.map Prod.fst).reverse) ((L.map Prod.snd).reverse)
      (r :: hrest) := hhigh_cons ▸ hhigh
  have hlast_mid : ((N.map Prod.snd) ++ [r]).getLast?
      = some r := by
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    simp only [List.getLast?_singleton]
  have hfull := chain_append g k ((L.map Prod.snd) ++ [mid])
    ((L.map Prod.fst) ++ [mid]) ((N.map Prod.snd) ++ [r])
    hlow_mid ((L.map Prod.fst).reverse)
    ((L.map Prod.snd).reverse) r hrest hhigh_rw hlast_mid
  have hhead_low : (N.map Prod.snd).head? = some 0 := by
    rw [List.head?_map, hhead]
    rfl
  obtain ⟨cs1rest, hcs1⟩ :=
    List.head?_eq_some_iff.mp hhead_low
  have hfull_cs : ((N.map Prod.snd) ++ [r]) ++ hrest
      = 0 :: ((cs1rest ++ [r]) ++ hrest) := by
    rw [hcs1, List.cons_append, List.cons_append,
      List.append_assoc]
  have hlast_high : ((N.map Prod.fst).reverse).getLast?
      = some 0 := by
    rw [List.getLast?_reverse, List.head?_map, hhead]
    rfl
  have hrest_last : hrest.getLast? = some 0 := by
    have h1 : ((N.map Prod.fst).reverse).getLast?
        = hrest.getLast? := by
      rw [hhigh_cons]
      exact List.getLast?_cons_of_ne_nil hrest_ne
    rw [hlast_high] at h1
    exact h1.symm
  have hfull_last : (((N.map Prod.snd) ++ [r]) ++ hrest).getLast?
      = some 0 := by
    rw [List.getLast?_append_of_ne_nil _ hrest_ne]
    exact hrest_last
  have hbal := chain_balance g k (((L.map Prod.snd) ++ [mid])
      ++ (L.map Prod.fst).reverse)
    (((L.map Prod.fst) ++ [mid]) ++ (L.map Prod.snd).reverse)
    (((N.map Prod.snd) ++ [r]) ++ hrest) hfull 0 hfull_last
    0 ((cs1rest ++ [r]) ++ hrest) hfull_cs
  have hxs_eq : ((L.map Prod.snd) ++ [mid])
      ++ (L.map Prod.fst).reverse
      = (reconOdd L mid).reverse := by
    rw [reconOdd_reverse L mid, List.append_assoc]
  have hys_eq : ((L.map Prod.fst) ++ [mid])
      ++ (L.map Prod.snd).reverse
      = reconOdd L mid := by
    unfold reconOdd
    rw [List.append_assoc]
  rw [hxs_eq, hys_eq] at hbal
  have hbal_simple : k * Nat.ofDigits g (reconOdd L mid).reverse
      = Nat.ofDigits g (reconOdd L mid) := by
    simp only [Nat.add_zero, Nat.zero_mul] at hbal
    exact hbal
  have h1 := digitValue_eq g (reconOdd L mid)
  have h2 := digitValue_eq g (reconOdd L mid).reverse
  rw [h1, h2, List.reverse_reverse]
  exact hbal_simple

private theorem labelsOf_reconEven (L : List (ℕ × ℕ)) :
    labelsOf (reconEven L) = L := by
  have hdiv : (reconEven L).length / 2 = L.length := by
    rw [reconEven_length]
    omega
  unfold labelsOf
  rw [hdiv]
  have hlenA : (L.map Prod.fst).length = L.length :=
    List.length_map Prod.fst
  have htake1 : (reconEven L).take L.length
      = L.map Prod.fst := by
    unfold reconEven
    rw [← hlenA, List.take_left]
  have hlenB : (L.map Prod.snd).length = L.length :=
    List.length_map Prod.snd
  have htake2 : (reconEven L).reverse.take L.length
      = L.map Prod.snd := by
    rw [reconEven_reverse L, ← hlenB, List.take_left]
  rw [htake1, htake2, zip_map_roundtrip]

private theorem labelsOf_reconOdd (L : List (ℕ × ℕ))
    (mid : ℕ) : labelsOf (reconOdd L mid) = L := by
  have hdiv : (reconOdd L mid).length / 2 = L.length := by
    rw [reconOdd_length]
    omega
  unfold labelsOf
  rw [hdiv]
  have hlenA : (L.map Prod.fst).length = L.length :=
    List.length_map Prod.fst
  have htake1 : (reconOdd L mid).take L.length
      = L.map Prod.fst := by
    unfold reconOdd
    rw [List.append_assoc, ← hlenA, List.take_left]
  have hlenB : (L.map Prod.snd).length = L.length :=
    List.length_map Prod.snd
  have htake2 : (reconOdd L mid).reverse.take L.length
      = L.map Prod.snd := by
    rw [reconOdd_reverse L mid, List.append_assoc, ← hlenB,
      List.take_left]
  rw [htake1, htake2, zip_map_roundtrip]

private theorem middle_unique (k r s g mid1 mid2 : ℕ)
    (hk : 2 ≤ k)
    (h1 : k * mid1 + s = mid1 + r * g)
    (h2 : k * mid2 + s = mid2 + r * g) :
    mid1 = mid2 := by
  have hL1 : k * mid1 + s + mid2
      = mid1 + r * g + mid2 := by rw [h1]
  have hL2 : k * mid2 + s + mid1
      = mid2 + r * g + mid1 := by rw [h2]
  have hR : mid1 + r * g + mid2
      = mid2 + r * g + mid1 := by ring
  have heq0 : k * mid1 + s + mid2
      = k * mid2 + s + mid1 := by
    rw [hL1, hL2]
    exact hR
  have e1 : k * mid1 + s + mid2
      = (k * mid1 + mid2) + s := by ring
  have e2 : k * mid2 + s + mid1
      = (k * mid2 + mid1) + s := by ring
  rw [e1, e2] at heq0
  have heq1 : k * mid1 + mid2 = k * mid2 + mid1 :=
    Nat.add_right_cancel heq0
  obtain ⟨j, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have e3 : j.succ * mid1 + mid2
      = j * mid1 + (mid1 + mid2) := by
    rw [Nat.succ_mul]
    ring
  have e4 : j.succ * mid2 + mid1
      = j * mid2 + (mid2 + mid1) := by
    rw [Nat.succ_mul]
    ring
  rw [e3, e4] at heq1
  have hcomm : mid1 + mid2 = mid2 + mid1 :=
    Nat.add_comm _ _
  rw [hcomm] at heq1
  have heq2 : j * mid1 = j * mid2 :=
    Nat.add_right_cancel heq1
  have hjpos : 0 < j := by omega
  exact Nat.mul_left_cancel hjpos heq2

private theorem reverse_take_even_aux (A B : List ℕ) (r : ℕ)
    (hrest : List ℕ)
    (hBrev : B.reverse = r :: hrest)
    (hA_last : A.getLast? = some r) :
    ((A ++ hrest).reverse.take B.length) = B := by
  have hB_eq : B = hrest.reverse ++ [r] := by
    have h1 : B.reverse.reverse = B := List.reverse_reverse B
    rw [hBrev, List.reverse_cons] at h1
    exact h1.symm
  have hrev_eq : (A ++ hrest).reverse
      = hrest.reverse ++ A.reverse := by
    rw [List.reverse_append]
  rw [hrev_eq]
  have hlen_hr : hrest.reverse.length = B.length - 1 := by
    have h1 : (B.reverse).length = B.length :=
      List.length_reverse
    rw [hBrev] at h1
    simp only [List.length_cons] at h1
    rw [List.length_reverse]
    omega
  have hBpos : 0 < B.length := by
    have h1 : (B.reverse).length = hrest.length + 1 := by
      rw [hBrev]
      simp only [List.length_cons]
    rw [List.length_reverse] at h1
    omega
  have htake_eq : ((hrest.reverse ++ A.reverse).take B.length)
      = hrest.reverse ++ (A.reverse.take 1) := by
    rw [List.take_append]
    have htake_hr : hrest.reverse.take B.length
        = hrest.reverse := by
      apply List.take_of_length_le
      omega
    rw [htake_hr]
    have hsub : B.length - hrest.reverse.length = 1 := by omega
    rw [hsub]
  rw [htake_eq]
  have hA_rev_head : A.reverse.head? = some r := by
    rw [List.head?_reverse, hA_last]
  obtain ⟨Arest, hArev⟩ :=
    List.head?_eq_some_iff.mp hA_rev_head
  have htakeA1 : A.reverse.take 1 = [r] := by
    rw [hArev]
    simp only [List.take_succ_cons, List.take_zero]
  rw [htakeA1, hB_eq]

private theorem reverse_take_odd_aux (A B : List ℕ) (r : ℕ)
    (hrest : List ℕ)
    (hBrev : B.reverse = r :: hrest) :
    ((((A ++ [r]) ++ hrest).reverse.take B.length)) = B := by
  have hB_eq : B = hrest.reverse ++ [r] := by
    have h1 : B.reverse.reverse = B := List.reverse_reverse B
    rw [hBrev, List.reverse_cons] at h1
    exact h1.symm
  have hrev_eq : ((A ++ [r]) ++ hrest).reverse
      = (hrest.reverse ++ [r]) ++ A.reverse := by
    rw [List.reverse_append, List.reverse_append,
      List.reverse_singleton, ← List.append_assoc]
  rw [hrev_eq, hB_eq]
  exact List.take_left

private theorem nodesOf_reconEven (g k : ℕ) (hg : 0 < g)
    (hk0 : 0 < k) (L N : List (ℕ × ℕ))
    (hlen : N.length = L.length + 1)
    (hhead : N.head? = some (0, 0))
    (hforall : List.Forall₂
      (fun label endpoints =>
        k * label.2 + endpoints.1.2 = label.1 + endpoints.2.2 * g ∧
        k * label.1 + endpoints.2.1 = label.2 + endpoints.1.1 * g)
      L (N.zip N.tail))
    (hpivot : ∃ r, N.getLast? = some (r, r))
    (hexL : ∃ first rest,
      L = first :: rest ∧ first.1 ≠ 0 ∧ first.2 ≠ 0)
    (hdigL : ∀ l ∈ L, l.1 < g ∧ l.2 < g) :
    nodesOf g k (reconEven L) = N := by
  obtain ⟨r, hpiv⟩ := hpivot
  have hlow := low_chain_of_path g k L N hlen hforall
  have hhigh := high_chain_of_path g k L N hlen hforall
  have hlast_low : (N.map Prod.snd).getLast? = some r := by
    rw [List.getLast?_map, hpiv]
    rfl
  have hhead_high : ((N.map Prod.fst).reverse).head?
      = some r := by
    rw [List.head?_reverse, List.getLast?_map, hpiv]
    rfl
  obtain ⟨hrest, hhigh_cons⟩ :=
    List.head?_eq_some_iff.mp hhead_high
  have hhigh_rw : IsCarryChain g k
      ((L.map Prod.fst).reverse) ((L.map Prod.snd).reverse)
      (r :: hrest) := hhigh_cons ▸ hhigh
  have hfull := chain_append g k (L.map Prod.snd)
    (L.map Prod.fst) (N.map Prod.snd) hlow
    ((L.map Prod.fst).reverse) ((L.map Prod.snd).reverse)
    r hrest hhigh_rw hlast_low
  have hDdig : ∀ d ∈ reconEven L, d < g :=
    reconEven_mem_lt g L hdigL
  have hDbal := bwd_even_balance g k L N hlen hhead
    hforall ⟨r, hpiv⟩ hexL
  have hcanon := canon_of_revMult g k hg hk0 (reconEven L)
    hDdig hDbal
  obtain ⟨hdig_eq, hlast_canon, hall_canon, hchain_canon⟩ :=
    hcanon
  have hxs_eq : (L.map Prod.snd) ++ (L.map Prod.fst).reverse
      = (reconEven L).reverse := by
    rw [reconEven_reverse L]
  have hys_eq : (L.map Prod.fst) ++ (L.map Prod.snd).reverse
      = reconEven L := rfl
  have hpath_rw : IsCarryChain g k (reconEven L).reverse
      (reconEven L) ((N.map Prod.snd) ++ hrest) := by
    have h1 : IsCarryChain g k (reconEven L).reverse
        ((L.map Prod.fst) ++ (L.map Prod.snd).reverse)
        ((N.map Prod.snd) ++ hrest) := hxs_eq ▸ hfull
    exact hys_eq ▸ h1
  obtain ⟨t1, hC0_canon⟩ := carriesOf_form g k (reconEven L)
  have hhead_low : (N.map Prod.snd).head? = some 0 := by
    rw [List.head?_map, hhead]
    rfl
  obtain ⟨cs1rest, hcs1⟩ :=
    List.head?_eq_some_iff.mp hhead_low
  have hC0_path : (N.map Prod.snd) ++ hrest
      = 0 :: (cs1rest ++ hrest) := by
    rw [hcs1, List.cons_append]
  have hCeq : carriesOf g k (reconEven L)
      = (N.map Prod.snd) ++ hrest :=
    chain_unique g hg k (reconEven L).reverse (reconEven L)
      (carriesOf g k (reconEven L)) hchain_canon
      ((N.map Prod.snd) ++ hrest) hpath_rw 0 t1
      (cs1rest ++ hrest) hC0_canon hC0_path
  have hdiv : (reconEven L).length / 2 = L.length := by
    rw [reconEven_length]
    omega
  have hNlen : N.length = L.length + 1 := hlen
  have htake_amt : (reconEven L).length / 2 + 1 = N.length := by
    omega
  have hlenA : (N.map Prod.snd).length = N.length :=
    List.length_map Prod.snd
  have htake_low : (((N.map Prod.snd) ++ hrest).take N.length)
      = N.map Prod.snd := by
    rw [← hlenA, List.take_left]
  have hBlen : (N.map Prod.fst).length = N.length :=
    List.length_map Prod.fst
  have htake_high : (((N.map Prod.snd) ++ hrest).reverse.take
      N.length) = N.map Prod.fst := by
    have h := reverse_take_even_aux (N.map Prod.snd)
      (N.map Prod.fst) r hrest hhigh_cons hlast_low
    rw [hBlen] at h
    exact h
  have hnodes_eq : nodesOf g k (reconEven L)
      = List.zip ((N.map Prod.fst)) (N.map Prod.snd) := by
    unfold nodesOf
    rw [hCeq, htake_amt, htake_high, htake_low]
  rw [hnodes_eq, zip_map_roundtrip]

private theorem nodesOf_reconOdd (g k : ℕ) (hg : 0 < g)
    (hk0 : 0 < k) (L N : List (ℕ × ℕ)) (mid r s : ℕ)
    (hlen : N.length = L.length + 1)
    (hhead : N.head? = some (0, 0))
    (hforall : List.Forall₂
      (fun label endpoints =>
        k * label.2 + endpoints.1.2 = label.1 + endpoints.2.2 * g ∧
        k * label.1 + endpoints.2.1 = label.2 + endpoints.1.1 * g)
      L (N.zip N.tail))
    (hpiv_last : N.getLast? = some (r, s))
    (hpiv_mid : k * mid + s = mid + r * g)
    (hmid_lt : mid < g)
    (hexL : ∃ first rest,
      L = first :: rest ∧ first.1 ≠ 0 ∧ first.2 ≠ 0)
    (hdigL : ∀ l ∈ L, l.1 < g ∧ l.2 < g) :
    nodesOf g k (reconOdd L mid) = N := by
  have hlow := low_chain_of_path g k L N hlen hforall
  have hhigh := high_chain_of_path g k L N hlen hforall
  have hmid_chain := chain_singleton g k mid mid s r hpiv_mid
  have hlast_low : (N.map Prod.snd).getLast? = some s := by
    rw [List.getLast?_map, hpiv_last]
    rfl
  have hlow_mid := chain_append g k (L.map Prod.snd)
    (L.map Prod.fst) (N.map Prod.snd) hlow [mid] [mid]
    s [r] hmid_chain hlast_low
  have hhead_high : ((N.map Prod.fst).reverse).head?
      = some r := by
    rw [List.head?_reverse, List.getLast?_map, hpiv_last]
    rfl
  obtain ⟨hrest, hhigh_cons⟩ :=
    List.head?_eq_some_iff.mp hhead_high
  have hhigh_rw : IsCarryChain g k
      ((L.map Prod.fst).reverse) ((L.map Prod.snd).reverse)
      (r :: hrest) := hhigh_cons ▸ hhigh
  have hlast_mid : ((N.map Prod.snd) ++ [r]).getLast?
      = some r := by
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    simp only [List.getLast?_singleton]
  have hfull := chain_append g k ((L.map Prod.snd) ++ [mid])
    ((L.map Prod.fst) ++ [mid]) ((N.map Prod.snd) ++ [r])
    hlow_mid ((L.map Prod.fst).reverse)
    ((L.map Prod.snd).reverse) r hrest hhigh_rw hlast_mid
  have hDdig : ∀ d ∈ reconOdd L mid, d < g :=
    reconOdd_mem_lt g L mid hmid_lt hdigL
  have hDbal := bwd_odd_balance g k L N mid r s hlen hhead
    hforall hpiv_last hpiv_mid hexL
  have hcanon := canon_of_revMult g k hg hk0 (reconOdd L mid)
    hDdig hDbal
  obtain ⟨hdig_eq, hlast_canon, hall_canon, hchain_canon⟩ :=
    hcanon
  have hxs_eq : ((L.map Prod.snd) ++ [mid])
      ++ (L.map Prod.fst).reverse
      = (reconOdd L mid).reverse := by
    rw [reconOdd_reverse L mid, List.append_assoc]
  have hys_eq : ((L.map Prod.fst) ++ [mid])
      ++ (L.map Prod.snd).reverse
      = reconOdd L mid := by
    unfold reconOdd
    rw [List.append_assoc]
  have hpath_rw : IsCarryChain g k (reconOdd L mid).reverse
      (reconOdd L mid) (((N.map Prod.snd) ++ [r]) ++ hrest) := by
    have h1 : IsCarryChain g k (reconOdd L mid).reverse
        (((L.map Prod.fst) ++ [mid])
          ++ (L.map Prod.snd).reverse)
        (((N.map Prod.snd) ++ [r]) ++ hrest) :=
      hxs_eq ▸ hfull
    exact hys_eq ▸ h1
  obtain ⟨t1, hC0_canon⟩ := carriesOf_form g k (reconOdd L mid)
  have hhead_low : (N.map Prod.snd).head? = some 0 := by
    rw [List.head?_map, hhead]
    rfl
  obtain ⟨cs1rest, hcs1⟩ :=
    List.head?_eq_some_iff.mp hhead_low
  have hC0_path : ((N.map Prod.snd) ++ [r]) ++ hrest
      = 0 :: ((cs1rest ++ [r]) ++ hrest) := by
    rw [hcs1, List.cons_append, List.cons_append,
      List.append_assoc]
  have hCeq : carriesOf g k (reconOdd L mid)
      = ((N.map Prod.snd) ++ [r]) ++ hrest :=
    chain_unique g hg k (reconOdd L mid).reverse
      (reconOdd L mid) (carriesOf g k (reconOdd L mid))
      hchain_canon (((N.map Prod.snd) ++ [r]) ++ hrest)
      hpath_rw 0 t1 ((cs1rest ++ [r]) ++ hrest)
      hC0_canon hC0_path
  have hdiv : (reconOdd L mid).length / 2 = L.length := by
    rw [reconOdd_length]
    omega
  have htake_amt : (reconOdd L mid).length / 2 + 1
      = N.length := by omega
  have hlenA : (N.map Prod.snd).length = N.length :=
    List.length_map Prod.snd
  have htake_low : ((((N.map Prod.snd) ++ [r]) ++ hrest).take
      N.length) = N.map Prod.snd := by
    rw [List.append_assoc, ← hlenA, List.take_left]
  have hBlen : (N.map Prod.fst).length = N.length :=
    List.length_map Prod.fst
  have htake_high : ((((N.map Prod.snd) ++ [r]) ++ hrest).reverse.take
      N.length) = N.map Prod.fst := by
    have h := reverse_take_odd_aux (N.map Prod.snd)
      (N.map Prod.fst) r hrest hhigh_cons
    rw [hBlen] at h
    exact h
  have hnodes_eq : nodesOf g k (reconOdd L mid)
      = List.zip (N.map Prod.fst) (N.map Prod.snd) := by
    unfold nodesOf
    rw [hCeq, htake_amt, htake_high, htake_low]
  rw [hnodes_eq, zip_map_roundtrip]

/-! # Young's correspondence for reverse multiples
-/

/--
**Young's theorem on reverse multiples.** Let $g$ and $k$ be natural numbers with $2 \le k < g$.
A $(g, k)$ reverse multiple is a list of base-$g$ digits $d_1, d_2, \dots, d_n$, most significant
first, with $n \ge 2$, $d_1 \ne 0$, $d_n \ne 0$ and $d_i < g$ for every $i$, such that $k$ times
the number $\sum_{i=1}^{n} d_i g^{n-i}$ equals the number $\sum_{i=1}^{n} d_{n+1-i} g^{n-i}$
whose digits are those of the first in reverse order. Consider the graph whose nodes are pairs
$(r, s)$ of natural numbers, with an edge labeled $(a, b)$ from $(r, s)$ to $(r', s')$ whenever
$k b + s = a + s' g$ and $k a + r' = b + r g$. A path is a sequence of nodes $v_0, \dots, v_m$
together with a sequence of labels $\ell_1, \dots, \ell_m$ such that $m \ge 1$, $v_0 = (0, 0)$,
both coordinates of every node are less than $k$, both coordinates of every label are less
than $g$, both coordinates of $\ell_1$ are nonzero, and for each $j$ the label $\ell_j$ labels an
edge from $v_{j-1}$ to $v_j$. A node $(r, s)$ is an even pivot if $r = s$, and an odd pivot if
for some $c < g$ there is an edge labeled $(c, c)$ from $(r, s)$ to $(s, r)$.

Then there is a bijection from the $(g, k)$ reverse multiples with an even number of digits to
the paths whose last node is an even pivot, and a bijection from the $(g, k)$ reverse multiples
with an odd number of digits to the paths whose last node is an odd pivot. Under both
bijections, a reverse multiple $d_1, \dots, d_n$ is sent to a path with labels
$(d_1, d_n), (d_2, d_{n-1}), \dots, (d_h, d_{n+1-h})$, where $h = \lfloor n/2 \rfloor$; in the
odd case, if $(r, s)$ is the last node of that path, there is an edge labeled
$(d_{h+1}, d_{h+1})$ from $(r, s)$ to $(s, r)$.

Proves `Wanted` entry `young_reverse_multiples_equiv_pivot_paths`.

Source: L. H. Kendrick, *Young Graphs: 1089 et al.*, Journal of Integer Sequences 18
(2015), Article 15.9.7, Theorem [Young's Theorem], lines 192-197,
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex>, after Theorems 1 and 2
of Young's first paper on reverse multiples.
-/
theorem young_reverse_multiples_equiv_pivot_paths
    (g k : ℕ) (hk : 2 ≤ k) (hkg : k < g) :
    let digitValue := fun digits : List ℕ =>
      digits.foldl (fun value digit => value * g + digit) 0
    let IsReverseMultiple := fun digits : List ℕ =>
      (∃ first middle last,
          digits = first :: middle ++ [last] ∧ first ≠ 0 ∧ last ≠ 0) ∧
        (∀ digit ∈ digits, digit < g) ∧
        k * digitValue digits = digitValue digits.reverse
    let Transition := fun (source : ℕ × ℕ) (label : ℕ × ℕ) (target : ℕ × ℕ) =>
      k * label.2 + source.2 = label.1 + target.2 * g ∧
        k * label.1 + target.1 = label.2 + source.1 * g
    let IsPath := fun path : List (ℕ × ℕ) × List (ℕ × ℕ) =>
      path.2.length = path.1.length + 1 ∧
        path.2.head? = some (0, 0) ∧
        (∀ node ∈ path.2, node.1 < k ∧ node.2 < k) ∧
        (∀ label ∈ path.1, label.1 < g ∧ label.2 < g) ∧
        (∃ first rest,
          path.1 = first :: rest ∧ first.1 ≠ 0 ∧ first.2 ≠ 0) ∧
        List.Forall₂
          (fun label endpoints => Transition endpoints.1 label endpoints.2)
          path.1 (path.2.zip path.2.tail)
    let EvenReverseMultiples :=
      {digits : List ℕ // IsReverseMultiple digits ∧ Even digits.length}
    let OddReverseMultiples :=
      {digits : List ℕ // IsReverseMultiple digits ∧ Odd digits.length}
    let PathsToEvenPivots :=
      {path : List (ℕ × ℕ) × List (ℕ × ℕ) //
        IsPath path ∧ ∃ r, path.2.getLast? = some (r, r)}
    let PathsToOddPivots :=
      {path : List (ℕ × ℕ) × List (ℕ × ℕ) //
        IsPath path ∧
          ∃ r s middle,
            path.2.getLast? = some (r, s) ∧ middle < g ∧
              Transition (r, s) (middle, middle) (s, r)}
    ∃ evenCorrespondence : EvenReverseMultiples ≃ PathsToEvenPivots,
      ∃ oddCorrespondence : OddReverseMultiples ≃ PathsToOddPivots,
        (∀ reverseMultiple,
          (evenCorrespondence reverseMultiple).1.1 =
            List.zip
              (reverseMultiple.1.take (reverseMultiple.1.length / 2))
              (reverseMultiple.1.reverse.take (reverseMultiple.1.length / 2))) ∧
        (∀ reverseMultiple,
          (oddCorrespondence reverseMultiple).1.1 =
              List.zip
                (reverseMultiple.1.take (reverseMultiple.1.length / 2))
                (reverseMultiple.1.reverse.take (reverseMultiple.1.length / 2)) ∧
            ∃ middle r s,
              (reverseMultiple.1.drop (reverseMultiple.1.length / 2)).head? =
                some middle ∧
              (oddCorrespondence reverseMultiple).1.2.getLast? = some (r, s) ∧
              Transition (r, s) (middle, middle) (s, r)) := by
  intro digitValue IsReverseMultiple Transition IsPath
    EvenReverseMultiples OddReverseMultiples
    PathsToEvenPivots PathsToOddPivots
  have hg : 0 < g := by omega
  have hk0 : 0 < k := by omega
  refine ⟨?evenCorr, ?oddCorr, ?evenLabels, ?oddLabels⟩
  · refine
      { toFun := ?toEven
        invFun := ?invEven
        left_inv := ?leftEven
        right_inv := ?rightEven }
    · intro D
      refine ⟨(labelsOf D.1, nodesOf g k D.1), ?_, ?_⟩
      · obtain ⟨⟨hex, hdig, hbal⟩, heven⟩ := D.2
        have hcanon := canon_of_revMult g k hg hk0 D.1 hdig hbal
        obtain ⟨hdig_eq, hlast_canon, hall_canon, hchain⟩ :=
          hcanon
        have hlen2 := revMult_len_ge_two D.1 hex
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [nodesOf_length, labelsOf_length]
        · exact nodesOf_head g k D.1 hlast_canon
        · intro node hmem
          exact nodesOf_mem_lt g k D.1 hall_canon node hmem
        · intro label hmem
          exact labelsOf_mem_lt g D.1 hdig label hmem
        · exact labelsOf_first_nonzero D.1 hex
        · exact fwd_forall2 g k D.1 hchain hlen2
      · obtain ⟨⟨hex, hdig, hbal⟩, heven⟩ := D.2
        exact fwd_pivot_even g k D.1 heven
    · intro P
      refine ⟨reconEven P.1.1, ?_⟩
      obtain ⟨⟨hlen, hhead, hnode_lt, hlabel_lt, hexL, hforall⟩,
        hpivot⟩ := P.2
      have hexD := reconEven_nonzero P.1.1 hexL
      have hdigD : ∀ d ∈ reconEven P.1.1, d < g := fun d hmem =>
        reconEven_mem_lt g P.1.1 hlabel_lt d hmem
      have hbalD := bwd_even_balance g k P.1.1 P.1.2 hlen hhead
        hforall hpivot hexL
      have hevenD := reconEven_length_even P.1.1
      exact ⟨⟨hexD, hdigD, hbalD⟩, hevenD⟩
    · intro D
      apply Subtype.ext
      dsimp only
      obtain ⟨⟨hex, hdig, hbal⟩, heven⟩ := D.2
      have h2m := Nat.two_mul_div_two_of_even heven
      exact reconEven_labelsOf_even D.1 (D.1.length / 2) rfl h2m
    · intro P
      apply Subtype.ext
      dsimp only
      obtain ⟨⟨hlen, hhead, hnode_lt, hlabel_lt, hexL, hforall⟩,
        hpivot⟩ := P.2
      have hlab := labelsOf_reconEven P.1.1
      have hnod := nodesOf_reconEven g k hg hk0 P.1.1 P.1.2
        hlen hhead hforall hpivot hexL hlabel_lt
      apply Prod.ext
      · exact hlab
      · exact hnod
  · refine
      { toFun := ?toOdd
        invFun := ?invOdd
        left_inv := ?leftOdd
        right_inv := ?rightOdd }
    · intro D
      refine ⟨(labelsOf D.1, nodesOf g k D.1), ?_, ?_⟩
      · obtain ⟨⟨hex, hdig, hbal⟩, hodd⟩ := D.2
        have hcanon := canon_of_revMult g k hg hk0 D.1 hdig hbal
        obtain ⟨hdig_eq, hlast_canon, hall_canon, hchain⟩ :=
          hcanon
        have hlen2 := revMult_len_ge_two D.1 hex
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [nodesOf_length, labelsOf_length]
        · exact nodesOf_head g k D.1 hlast_canon
        · intro node hmem
          exact nodesOf_mem_lt g k D.1 hall_canon node hmem
        · intro label hmem
          exact labelsOf_mem_lt g D.1 hdig label hmem
        · exact labelsOf_first_nonzero D.1 hex
        · exact fwd_forall2 g k D.1 hchain hlen2
      · obtain ⟨⟨hex, hdig, hbal⟩, hodd⟩ := D.2
        have hcanon := canon_of_revMult g k hg hk0 D.1 hdig hbal
        obtain ⟨hdig_eq, hlast_canon, hall_canon, hchain⟩ :=
          hcanon
        have hpiv := fwd_pivot_odd g k D.1 hchain hdig hodd
        obtain ⟨r, s, mid, hlast, hmid_lt, htrans, hdrop⟩ :=
          hpiv
        exact ⟨r, s, mid, hlast, hmid_lt, htrans⟩
    · intro P
      have hex_mid : ∃ mid, ∃ r s,
          P.1.2.getLast? = some (r, s) ∧ mid < g ∧
            (k * mid + s = mid + r * g ∧
              k * mid + s = mid + r * g) := by
        obtain ⟨⟨hlen, hhead, hnode_lt, hlabel_lt, hexL,
          hforall⟩, r, s, mid, hlast, hmid_lt, htrans⟩ := P.2
        exact ⟨mid, r, s, hlast, hmid_lt, htrans⟩
      refine ⟨reconOdd P.1.1 (Classical.choose hex_mid), ?_⟩
      have hspec := Classical.choose_spec hex_mid
      obtain ⟨r, s, hlast, hmid_lt, htrans⟩ := hspec
      obtain ⟨⟨hlen, hhead, hnode_lt, hlabel_lt, hexL,
        hforall⟩, hpivot⟩ := P.2
      have hexD := reconOdd_nonzero P.1.1
        (Classical.choose hex_mid) hexL
      have hdigD : ∀ d ∈ reconOdd P.1.1
          (Classical.choose hex_mid), d < g :=
        fun d hmem => reconOdd_mem_lt g P.1.1
          (Classical.choose hex_mid) hmid_lt hlabel_lt d hmem
      have hbalD := bwd_odd_balance g k P.1.1 P.1.2
        (Classical.choose hex_mid) r s hlen hhead hforall
        hlast htrans.1 hexL
      have hoddD := reconOdd_length_odd P.1.1
        (Classical.choose hex_mid)
      exact ⟨⟨hexD, hdigD, hbalD⟩, hoddD⟩
    · intro D
      apply Subtype.ext
      dsimp only
      obtain ⟨⟨hex, hdig, hbal⟩, hodd⟩ := D.2
      have hcanon := canon_of_revMult g k hg hk0 D.1 hdig hbal
      obtain ⟨hdig_eq, hlast_canon, hall_canon, hchain⟩ :=
        hcanon
      have hpiv0 := fwd_pivot_odd g k D.1 hchain hdig hodd
      obtain ⟨r0, s0, mid0, hlast0, hmid0_lt, htrans0,
        hdrop0⟩ := hpiv0
      have hex_mid'' : ∃ mid, ∃ r s,
          (nodesOf g k D.1).getLast? = some (r, s) ∧ mid < g ∧
            (k * mid + s = mid + r * g ∧
              k * mid + s = mid + r * g) :=
        ⟨mid0, r0, s0, hlast0, hmid0_lt, htrans0⟩
      have hspec'' := Classical.choose_spec hex_mid''
      obtain ⟨r1, s1, hlast1, hmid1_lt, htrans1⟩ := hspec''
      have heq_some : some (r1, s1) = some (r0, s0) := by
        rw [← hlast1, hlast0]
      have heq_pair : (r1, s1) = (r0, s0) :=
        Option.some_inj.mp heq_some
      have hr : r1 = r0 := congrArg Prod.fst heq_pair
      have hs : s1 = s0 := congrArg Prod.snd heq_pair
      rw [hr, hs] at htrans1
      have hmid_eq : Classical.choose hex_mid'' = mid0 :=
        middle_unique k r0 s0 g
          (Classical.choose hex_mid'') mid0 hk htrans1.1
          htrans0.1
      have hodd_eq : D.1.length / 2 * 2 + 1 = D.1.length :=
        Nat.div_two_mul_two_add_one_of_odd hodd
      have hrecon0 := reconOdd_labelsOf_odd D.1
        (D.1.length / 2) mid0 rfl hodd_eq hdrop0
      have hgoal : reconOdd (labelsOf D.1)
          (Classical.choose hex_mid'') = D.1 := by
        rw [hmid_eq]
        exact hrecon0
      exact hgoal
    · intro P
      apply Subtype.ext
      dsimp only
      obtain ⟨⟨hlen, hhead, hnode_lt, hlabel_lt, hexL, hforall⟩,
        hpivot⟩ := P.2
      have hex_mid'' : ∃ mid, ∃ r s,
          P.1.2.getLast? = some (r, s) ∧ mid < g ∧
            (k * mid + s = mid + r * g ∧
              k * mid + s = mid + r * g) := by
        obtain ⟨r, s, mid, hlast, hmid_lt, htrans⟩ := hpivot
        exact ⟨mid, r, s, hlast, hmid_lt, htrans⟩
      have hspec'' := Classical.choose_spec hex_mid''
      obtain ⟨r1, s1, hlast1, hmid1_lt, htrans1⟩ := hspec''
      have hlab := labelsOf_reconOdd P.1.1
        (Classical.choose hex_mid'')
      have hnod := nodesOf_reconOdd g k hg hk0 P.1.1 P.1.2
        (Classical.choose hex_mid'') r1 s1 hlen hhead
        hforall hlast1 htrans1.1 hmid1_lt hexL hlabel_lt
      apply Prod.ext
      · exact hlab
      · exact hnod
  · intro D
    rfl
  · intro D
    constructor
    · rfl
    · obtain ⟨⟨hex, hdig, hbal⟩, hodd⟩ := D.2
      have hcanon := canon_of_revMult g k hg hk0 D.1 hdig hbal
      obtain ⟨hdig_eq, hlast_canon, hall_canon, hchain⟩ :=
        hcanon
      have hpiv0 := fwd_pivot_odd g k D.1 hchain hdig hodd
      obtain ⟨r0, s0, mid0, hlast0, hmid0_lt, htrans0,
        hdrop0⟩ := hpiv0
      exact ⟨mid0, r0, s0, hdrop0, hlast0, htrans0⟩

end MetaMathlibExt
end
