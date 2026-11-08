/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Online.Paging
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Card

/-!
# No deterministic online paging algorithm beats `k`

The lower bound matching `lruMisses_le` (Sleator and Tarjan, *Amortized efficiency of list update
and paging rules*, CACM 1985; Borodin and El-Yaniv, *Online Computation and Competitive
Analysis*, Chapter 3): with `k + 1` pages, an adversary that always requests the
page a deterministic online algorithm does not hold forces a miss on every request, while an
offline algorithm misses at most once every `k` requests.

Main results:

* `OnlinePager`: a deterministic online paging algorithm is any state machine whose cache never
  holds more than `k` pages (its moves need not even be legal, which only strengthens the bound);
  `lruPager` is LRU as such a machine (`lruPager_misses`).
* `misses_adversary`: on the adversary's sequence (`adversary`, `outside`) the pager misses every
  request.
* `optStep`, `optTrace`, `optTrace_legal`, `misses_optTrace_le`: an offline strategy (on a miss,
  evict a page not among the next `k - 1` requests) is a legal trace of `cacheLTS k` and misses
  at most `k - |c| + ⌈n / k⌉` times on `n` requests over `k + 1` pages.
* `adversary_vs_optimum`: the pager misses `n` times while the optimal furthest-in-future manager
  misses at most `k + ⌈n / k⌉` times.
* `not_competitive_of_lt` (**no deterministic online pager is better than `k`-competitive**): for
  every ratio `c / d < k` and additive constant `b` some sequence makes `d` times the pager's
  misses exceed `c * OPT + b`.

## Cost model

The cost is the number of misses; there is no computation to charge.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Online.Paging

open Cslib.Algorithms.Lean.OfflineCaching

/-! ## Online pagers and the adversary -/

/-- A deterministic online paging algorithm with cache size `k`: a state machine whose cache
never holds more than `k` pages. Its moves need not be legal transitions; the lower bound holds
for any such machine. -/
structure OnlinePager.{u, v} (α : Type u) (k : ℕ) where
  /-- Internal states. -/
  State : Type v
  /-- The initial state. -/
  init : State
  /-- The pages cached in a state. -/
  cache : State → List α
  /-- The state after serving a request. -/
  step : State → α → State
  /-- The cache holds at most `k` pages. -/
  cache_le : ∀ q, (cache q).length ≤ k

namespace OnlinePager

variable {α : Type*} [DecidableEq α] {k : ℕ} (A : OnlinePager α k)

/-- The misses of an online pager: requests for pages not in its cache. -/
def misses : A.State → List α → ℕ
  | _, [] => 0
  | q, p :: σ => (if p ∈ A.cache q then 0 else 1) + misses (A.step q p) σ

end OnlinePager

/-- LRU as an online pager. -/
def lruPager.{u} (α : Type u) [DecidableEq α] (k : ℕ) : OnlinePager.{u, u} α k where
  State := {c : List α // c.length ≤ k}
  init := ⟨[], Nat.zero_le _⟩
  cache q := q.1
  step q p := ⟨lruStep k q.1 p, List.length_take_le _ _⟩
  cache_le q := q.2

/-- The online pager `lruPager` misses exactly as `lruMisses` counts. -/
theorem lruPager_misses {α : Type*} [DecidableEq α] {k : ℕ} :
    ∀ (q : (lruPager α k).State) (σ : List α), (lruPager α k).misses q σ = lruMisses k q.1 σ
  | _, [] => rfl
  | q, p :: σ => by
      simp only [OnlinePager.misses, lruMisses]
      rw [lruPager_misses _ σ]
      rfl

/-- A page of `Fin (k + 1)` outside a cache (when there is one). -/
def outside {k : ℕ} (c : List (Fin (k + 1))) : Fin (k + 1) :=
  ((List.finRange (k + 1)).find? fun x => x ∉ c).getD 0

/-- A cache of at most `k` pages misses one of the `k + 1` pages. -/
theorem outside_not_mem {k : ℕ} {c : List (Fin (k + 1))} (hc : c.length ≤ k) : outside c ∉ c := by
  unfold outside
  cases h : (List.finRange (k + 1)).find? fun x => x ∉ c with
  | some x => simpa using List.find?_some h
  | none =>
      exfalso
      have hall : ∀ x ∈ List.finRange (k + 1), x ∈ c := fun x hx => by
        have := List.find?_eq_none.1 h x hx
        simpa using this
      have := ((List.nodup_finRange (k + 1)).subperm hall).length_le
      rw [List.length_finRange] at this
      omega

/-- The adversary: always request the page the pager does not hold. -/
def adversary {k : ℕ} (A : OnlinePager (Fin (k + 1)) k) : ℕ → A.State → List (Fin (k + 1))
  | 0, _ => []
  | n + 1, q => outside (A.cache q) :: adversary A n (A.step q (outside (A.cache q)))

theorem length_adversary {k : ℕ} (A : OnlinePager (Fin (k + 1)) k) :
    ∀ n q, (adversary A n q).length = n
  | 0, _ => rfl
  | n + 1, q => by simp [adversary, length_adversary A n]

/-- **The pager misses every request** of the adversary's sequence. -/
theorem misses_adversary {k : ℕ} (A : OnlinePager (Fin (k + 1)) k) :
    ∀ n q, A.misses q (adversary A n q) = n
  | 0, _ => rfl
  | n + 1, q => by
      simp only [adversary, OnlinePager.misses, outside_not_mem (A.cache_le q), ↓reduceIte,
        misses_adversary A n]
      omega

/-! ## An offline strategy that misses once every `k` requests -/

section Offline

variable {α : Type*} [DecidableEq α]

/-- The offline step: on a miss with a full cache, evict a page not requested among the next
`k - 1` requests. -/
def optStep (k : ℕ) (c : List α) (p : α) (future : List α) : CacheEvent α × List α :=
  if p ∈ c then (.hit p, c)
  else if c.length < k then (.miss p none, p :: c)
  else match c.find? (fun x => x ∉ future.take (k - 1)) with
    | some v => (.miss p (some v), p :: c.erase v)
    | none => (.miss p none, p :: c)

/-- The offline trace. -/
def optTrace (k : ℕ) : List α → List α → List (CacheEvent α)
  | _, [] => []
  | c, p :: rest => (optStep k c p rest).1 :: optTrace k (optStep k c p rest).2 rest

/-- A full cache of `k` distinct pages has a page outside any `k - 1` requests. -/
theorem find?_isSome {k : ℕ} (hk : 1 ≤ k) {c : List α} (hnd : c.Nodup) (hck : c.length = k)
    (future : List α) : ∃ v, c.find? (fun x => x ∉ future.take (k - 1)) = some v := by
  cases h : c.find? (fun x => x ∉ future.take (k - 1)) with
  | some v => exact ⟨v, rfl⟩
  | none =>
      exfalso
      have hall : ∀ x ∈ c, x ∈ future.take (k - 1) := fun x hx => by
        simpa using List.find?_eq_none.1 h x hx
      have := (hnd.subperm hall).length_le
      have := List.length_take_le (k - 1) future
      omega

/-- **Each offline step is a legal transition** and keeps the cache valid. -/
theorem optStep_tr {k : ℕ} (hk : 1 ≤ k) {c : List α} (hnd : c.Nodup) (hck : c.length ≤ k)
    (p : α) (future : List α) :
    (cacheLTS k).Tr c (optStep k c p future).1 (optStep k c p future).2 := by
  unfold optStep
  by_cases hp : p ∈ c
  · simp only [hp, ↓reduceIte]
    exact ⟨hp, List.Perm.refl _⟩
  · simp only [hp, ↓reduceIte]
    by_cases hlt : c.length < k
    · simp only [hlt, ↓reduceIte]
      exact ⟨hp, Or.inr ⟨hlt, List.Perm.refl _⟩⟩
    · simp only [hlt, ↓reduceIte]
      obtain ⟨v, hv⟩ := find?_isSome hk hnd (by omega) future
      rw [hv]
      exact ⟨by omega, hp, by omega, List.mem_of_find?_eq_some hv, List.Perm.refl _⟩

/-- **The offline trace is legal** and serves exactly the requests. -/
theorem optTrace_legal {k : ℕ} (hk : 1 ≤ k) : ∀ (c σ : List α), c.Nodup → c.length ≤ k →
    (∃ cf, (cacheLTS k).MTr c (optTrace k c σ) cf) ∧ (optTrace k c σ).map CacheEvent.request = σ
  | c, [], _, _ => ⟨⟨c, Cslib.LTS.MTr.refl⟩, rfl⟩
  | c, p :: rest, hnd, hck => by
      have htr := optStep_tr hk hnd hck p rest
      obtain ⟨hnd', hck'⟩ := cacheLTS_valid htr hnd hck
      obtain ⟨⟨cf, hcf⟩, hmap⟩ := optTrace_legal hk _ rest hnd' hck'
      refine ⟨⟨cf, Cslib.LTS.MTr.stepL htr hcf⟩, ?_⟩
      simp only [optTrace, List.map_cons, hmap]
      congr 1
      unfold optStep
      split_ifs
      · rfl
      · rfl
      · split <;> rfl

/-- Hits leave the offline trace's later misses unchanged. -/
theorem misses_optTrace_hits {k : ℕ} : ∀ (w τ c : List α), (∀ x ∈ w, x ∈ c) →
    misses (optTrace k c (w ++ τ)) = misses (optTrace k c τ)
  | [], _, _, _ => rfl
  | p :: w, τ, c, h => by
      have hp : p ∈ c := h p List.mem_cons_self
      have hs : optStep k c p (w ++ τ) = (.hit p, c) := by simp [optStep, hp]
      simp only [List.cons_append, optTrace, hs]
      rw [misses, List.countP_cons_of_neg (by simp [CacheEvent.isMiss])]
      exact misses_optTrace_hits w τ c fun x hx => h x (List.mem_cons_of_mem _ hx)

end Offline

/-- With `k + 1` pages, a full cache misses only the evicted page. -/
theorem mem_of_full {k : ℕ} {c : List (Fin (k + 1))} (hnd : c.Nodup) (hck : c.length = k)
    {p v : Fin (k + 1)} (hp : p ∉ c) {x : Fin (k + 1)} (hx : x ≠ v) :
    x ∈ p :: c.erase v := by
  have hpc : x ∈ p :: c := by
    by_contra hxc
    have hnd' : (x :: p :: c).Nodup := List.nodup_cons.2 ⟨hxc, List.nodup_cons.2 ⟨hp, hnd⟩⟩
    have := hnd'.length_le_card
    simp only [List.length_cons, Fintype.card_fin] at this
    omega
  rcases List.mem_cons.1 hpc with rfl | hxc
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ ((List.Nodup.mem_erase_iff hnd).2 ⟨hx, hxc⟩)

/-- **The offline trace misses at most once every `k` requests**, after at most `k - |c|`
misses filling the cache. -/
theorem misses_optTrace_le {k : ℕ} (hk : 1 ≤ k) : ∀ (N : ℕ) (σ : List (Fin (k + 1))),
    σ.length ≤ N → ∀ c : List (Fin (k + 1)), c.Nodup → c.length ≤ k →
    misses (optTrace k c σ) ≤ (k - c.length) + (σ.length + k - 1) / k
  | _, [], _, c, _, _ => by simp [optTrace, misses]
  | 0, _ :: _, h, _, _, _ => by simp at h
  | N + 1, p :: rest, hN, c, hnd, hck => by
      have hmono : (rest.length + k - 1) / k ≤ (rest.length + 1 + k - 1) / k :=
        Nat.div_le_div_right (by omega)
      by_cases hp : p ∈ c
      · have hs : optStep k c p rest = (.hit p, c) := by simp [optStep, hp]
        have ih := misses_optTrace_le hk N rest (by simp at hN; omega) c hnd hck
        simp only [optTrace, hs, misses, List.countP_cons, CacheEvent.isMiss, List.length_cons]
          at ih ⊢
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        omega
      · by_cases hlt : c.length < k
        · have hs : optStep k c p rest = (.miss p none, p :: c) := by simp [optStep, hp, hlt]
          have ih := misses_optTrace_le hk N rest (by simp at hN; omega) (p :: c)
            (List.nodup_cons.2 ⟨hp, hnd⟩) (by simp only [List.length_cons]; omega)
          simp only [optTrace, hs, misses, List.countP_cons, CacheEvent.isMiss, List.length_cons]
            at ih ⊢
          simp only [↓reduceIte]
          omega
        · have hck' : c.length = k := by omega
          obtain ⟨v, hv⟩ := find?_isSome hk hnd hck' rest
          have hs : optStep k c p rest = (.miss p (some v), p :: c.erase v) := by
            simp only [optStep, hp, hlt, ↓reduceIte, hv]
          have hvc : v ∈ c := List.mem_of_find?_eq_some hv
          have hvw : v ∉ rest.take (k - 1) := by simpa using List.find?_some hv
          have hnd' : (p :: c.erase v).Nodup :=
            List.nodup_cons.2 ⟨fun h => hp (List.mem_of_mem_erase h), hnd.erase v⟩
          have hlen' : (p :: c.erase v).length = k := by
            rw [List.length_cons, List.length_erase_of_mem hvc]; omega
          -- the next `k - 1` requests all hit
          have hhit : ∀ x ∈ rest.take (k - 1), x ∈ p :: c.erase v := fun x hx =>
            mem_of_full hnd hck' hp (fun h => hvw (h ▸ hx))
          have hskip := misses_optTrace_hits (k := k) (rest.take (k - 1)) (rest.drop (k - 1))
            (p :: c.erase v) hhit
          rw [List.take_append_drop] at hskip
          have ih := misses_optTrace_le hk N (rest.drop (k - 1))
            (by simp only [List.length_drop]; simp at hN; omega) _ hnd' (by omega)
          rw [hlen', Nat.sub_self, Nat.zero_add, List.length_drop] at ih
          have hdiv : (rest.length - (k - 1) + k - 1) / k ≤ rest.length / k := by
            by_cases hr : k - 1 ≤ rest.length
            · exact Nat.div_le_div_right (by omega)
            · rw [Nat.div_eq_of_lt (by omega)]; exact Nat.zero_le _
          have hsucc : rest.length / k + 1 = (rest.length + 1 + k - 1) / k := by
            rw [show rest.length + 1 + k - 1 = rest.length + k by omega,
              Nat.add_div_right _ (by omega)]
          simp only [optTrace, hs, misses, List.countP_cons, CacheEvent.isMiss, List.length_cons]
            at hskip ih ⊢
          simp only [↓reduceIte]
          omega

/-! ## The lower bound -/

/-- **The adversary forces `n` misses while the optimum misses at most `k + ⌈n / k⌉` times**:
for every deterministic online pager with cache size `k ≥ 1` on `k + 1` pages and every `n`. -/
theorem adversary_vs_optimum {k : ℕ} (hk : 1 ≤ k) (A : OnlinePager (Fin (k + 1)) k) (n : ℕ) :
    A.misses A.init (adversary A n A.init) = n ∧
      misses (furthestInFuture k (adversary A n A.init) []).1 ≤ k + (n + k - 1) / k := by
  refine ⟨misses_adversary A n A.init, ?_⟩
  set σ := adversary A n A.init
  obtain ⟨⟨cf, hcf⟩, hmap⟩ := optTrace_legal hk ([] : List (Fin (k + 1))) σ List.nodup_nil
    (Nat.zero_le _)
  have hopt : misses (furthestInFuture k σ []).1 ≤ misses (optTrace k [] σ) :=
    furthestInFuture_misses_le k σ [] List.nodup_nil (Nat.zero_le _) _ cf hcf hmap
  have hle := misses_optTrace_le hk σ.length σ (le_refl _) [] List.nodup_nil (Nat.zero_le _)
  rw [length_adversary] at hle
  simp only [List.length_nil, Nat.sub_zero] at hle
  exact hopt.trans hle

/-- **No deterministic online pager is better than `k`-competitive**: for every ratio
`c / d < k` and every additive constant `b` there is a request sequence on which the pager misses
more than `c / d` times the optimum plus `b / d`. -/
theorem not_competitive_of_lt {k : ℕ} (hk : 1 ≤ k) (A : OnlinePager (Fin (k + 1)) k) {c d : ℕ}
    (hc : c < k * d) (b : ℕ) : ∃ σ : List (Fin (k + 1)),
      c * misses (furthestInFuture k σ []).1 + b < d * A.misses A.init σ := by
  set m := c * k + b + 1 with hm
  obtain ⟨h1, h2⟩ := adversary_vs_optimum hk A (k * m)
  refine ⟨adversary A (k * m) A.init, ?_⟩
  rw [h1]
  have hdiv : (k * m + k - 1) / k = m := by
    rw [show k * m + k - 1 = (k - 1) + m * k by rw [Nat.mul_comm]; omega,
      Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  rw [hdiv] at h2
  have hcm : (c + 1) * m ≤ (k * d) * m := Nat.mul_le_mul_right m hc
  have hdk : d * (k * m) = (k * d) * m := by rw [Nat.mul_left_comm, ← Nat.mul_assoc]
  have hlt : c * k + b < m := by omega
  calc c * misses (furthestInFuture k (adversary A (k * m) A.init) []).1 + b
      ≤ c * (k + m) + b := Nat.add_le_add_right (Nat.mul_le_mul_left c h2) b
    _ < d * (k * m) := by
        rw [hdk, Nat.mul_add]
        rw [Nat.succ_mul] at hcm
        omega

end Cslib.Algorithms.Lean.Online.Paging
