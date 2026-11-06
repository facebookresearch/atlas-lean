/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ext

@[expose] public section

/-! # Shapley value characterization for cooperative games

Existence and uniqueness of the linear value satisfying efficiency, symmetry,
and the null-player axiom, via unanimity games and Möbius inversion on the
Boolean lattice.

Source: L. S. Shapley, "A Value for n-Person Games," Contributions to the
Theory of Games II, Annals of Mathematics Studies 28, Princeton University
Press (1953), 307--317; modern DOI `10.1515/9781400881970-018`.

Source-fidelity note: Shapley's printed argument (pp. 308--312) works with
superadditive games on a player universe with finite carriers, with axioms of
full permutation equivariance, efficiency for every carrier, and aggregation.
What is proved here is an adapted fixed-finite-player vector-space
characterization: it quantifies over arbitrary normalized set functions on one
fixed finite player type, packages aggregation together with real homogeneity
as linearity, and uses invariant-game symmetry (equal payoffs when a
permutation fixes the game), grand-coalition efficiency, and a null-player
axiom. This characterization is mathematically coherent as stated, but it is
this adapted formulation rather than a literal transcription of the source
theorem.
-/

namespace MathlibExt.GameTheory.ShapleyValue

/-- **Cooperative game with transferable utility.** Given a set $N$ of players, a cooperative
game on $N$ is a function $v$ that assigns to every coalition $S \subseteq N$ a real number
$v(S)$, the worth of $S$, such that $v(\emptyset) = 0$. -/
@[ext]
structure CoopGame (Player : Type*) where
  charFun : Set Player → ℝ
  empty : charFun ∅ = 0

namespace CoopGame

variable {Player : Type*}

instance : AddCommGroup (CoopGame Player) where
  add v w :=
    ⟨fun S => v.charFun S + w.charFun S, by simp [v.empty, w.empty]⟩
  add_assoc a b c := by
    ext S
    exact add_assoc (a.charFun S) (b.charFun S) (c.charFun S)
  zero := ⟨fun _ => 0, rfl⟩
  zero_add a := by
    ext S
    exact zero_add (a.charFun S)
  add_zero a := by
    ext S
    exact add_zero (a.charFun S)
  nsmul n v :=
    ⟨fun S => n • v.charFun S, by simp [v.empty]⟩
  neg v :=
    ⟨fun S => -v.charFun S, by simp [v.empty]⟩
  zsmul n v :=
    ⟨fun S => n • v.charFun S, by simp [v.empty]⟩
  neg_add_cancel a := by
    ext S
    exact neg_add_cancel (a.charFun S)
  add_comm a b := by
    ext S
    exact add_comm (a.charFun S) (b.charFun S)

instance : SMul ℝ (CoopGame Player) where
  smul c v := ⟨fun S => c * v.charFun S, by simp [v.empty]⟩

instance : Module ℝ (CoopGame Player) where
  one_smul v := by
    ext S
    exact one_mul (v.charFun S)
  mul_smul c₁ c₂ v := by
    ext S
    exact mul_assoc c₁ c₂ (v.charFun S)
  smul_zero c := by
    ext S
    exact mul_zero c
  smul_add c v w := by
    ext S
    exact mul_add c (v.charFun S) (w.charFun S)
  add_smul c₁ c₂ v := by
    ext S
    exact add_mul c₁ c₂ (v.charFun S)
  zero_smul v := by
    ext S
    exact zero_mul (v.charFun S)

end CoopGame

variable {Player : Type*} [DecidableEq Player] [Fintype Player]

/-- **Null player.** Let $v$ be a cooperative game on a finite set $N$ of players. A player
$i \in N$ is a null player of $v$ if $v(S \cup \{i\}) = v(S)$ for every coalition
$S \subseteq N$ with $i \notin S$. -/
def IsNullPlayer (v : CoopGame Player) (i : Player) : Prop :=
  ∀ S : Set Player, i ∉ S → v.charFun (insert i S) = v.charFun S

/-- **Efficient value.** Let $N$ be a finite set of players and $\varphi$ an $\mathbb{R}$-linear
map from cooperative games on $N$ (added and scaled pointwise) to payoff vectors in
$\mathbb{R}^N$. Then $\varphi$ is efficient if for every game $v$ the payoffs add up to the worth
of the grand coalition: $\sum_{i \in N} \varphi(v)_i = v(N)$. -/
def IsEfficient (φ : CoopGame Player →ₗ[ℝ] (Player → ℝ)) : Prop :=
  ∀ v : CoopGame Player, ∑ i : Player, φ v i = v.charFun Set.univ

/-- **Symmetric value.** Let $N$ be a finite set of players and $\varphi$ an $\mathbb{R}$-linear
map from cooperative games on $N$ (added and scaled pointwise) to payoff vectors in
$\mathbb{R}^N$. Then $\varphi$ is symmetric if for every game $v$ and every permutation $\sigma$
of $N$ with $v(\sigma(S)) = v(S)$ for all coalitions $S \subseteq N$, every player $i$ satisfies
$\varphi(v)_{\sigma(i)} = \varphi(v)_i$. -/
def IsSymmetric (φ : CoopGame Player →ₗ[ℝ] (Player → ℝ)) : Prop :=
  ∀ (σ : Equiv.Perm Player) (v : CoopGame Player),
    (∀ S : Set Player, v.charFun (σ '' S) = v.charFun S) →
    ∀ i : Player, φ v (σ i) = φ v i

/-- **Null player axiom.** Let $N$ be a finite set of players and $\varphi$ an $\mathbb{R}$-linear
map from cooperative games on $N$ (added and scaled pointwise) to payoff vectors in
$\mathbb{R}^N$. Then $\varphi$ satisfies the null player axiom if $\varphi(v)_i = 0$ for every
game $v$ and every null player $i$ of $v$. -/
def SatisfiesNullPlayerAxiom (φ : CoopGame Player →ₗ[ℝ] (Player → ℝ)) : Prop :=
  ∀ (v : CoopGame Player) (i : Player), IsNullPlayer v i → φ v i = 0

-- Classical decidability for the subset tests in unanimity-game statements.
attribute [local instance] Classical.propDecidable

/-- Unanimity game: worth 1 iff `T ⊆ S` (zero game when `T = ∅`, since the
constant-1 function is not normalized). -/
private noncomputable def unanimity (T : Finset Player) : CoopGame Player := by
  classical
  exact if h : T = ∅ then 0
  else
    ⟨fun S => if (T : Set Player) ⊆ S then (1 : ℝ) else 0, by
      rw [ite_eq_right]
      intro hsub
      apply h
      exact Finset.coe_eq_empty.mp (Set.subset_empty_iff.mp hsub)⟩

omit [Fintype Player] in
private theorem unanimity_zero : unanimity (∅ : Finset Player) = 0 := by
  simp [unanimity]

omit [Fintype Player] in
private theorem unanimity_charFun {T : Finset Player} (hT : T ≠ ∅) (S : Set Player) :
    (unanimity T).charFun S = if (T : Set Player) ⊆ S then (1 : ℝ) else 0 := by
  classical
  simp [unanimity, dite_eq_right hT]

omit [DecidableEq Player] [Fintype Player] in
private theorem charFun_add (v w : CoopGame Player) (S : Set Player) :
    (v + w).charFun S = v.charFun S + w.charFun S :=
  rfl

omit [DecidableEq Player] [Fintype Player] in
private theorem charFun_smul (c : ℝ) (v : CoopGame Player) (S : Set Player) :
    (c • v).charFun S = c * v.charFun S :=
  rfl

omit [DecidableEq Player] [Fintype Player] in
private theorem charFun_zero (S : Set Player) : (0 : CoopGame Player).charFun S = 0 :=
  rfl

omit [DecidableEq Player] [Fintype Player] in
private theorem charFun_sum {ι : Type*} (s : Finset ι)
    (F : ι → CoopGame Player)
    (S : Set Player) :
    (∑ T ∈ s, F T).charFun S = ∑ T ∈ s, (F T).charFun S := by
  classical
  induction s using Finset.induction with
  | empty => simp [charFun_zero]
  | insert _ _ ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, charFun_add, ih]

/-- Möbius coefficient of `v` at `T`. -/
private noncomputable def mobiusCoeff (v : CoopGame Player) (T : Finset Player) : ℝ :=
  ∑ R ∈ T.powerset, (-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R

omit [DecidableEq Player] [Fintype Player] in
private theorem mobiusCoeff_empty (v : CoopGame Player) : mobiusCoeff v ∅ = 0 := by
  simp [mobiusCoeff, Finset.powerset_empty, Finset.coe_empty, v.empty]

omit [Fintype Player] in
/-- Alternating sum over a powerset. -/
private theorem sum_powerset_neg_one_pow_card (M : Finset Player) :
    ∑ U ∈ M.powerset, (-1 : ℝ) ^ U.card = (if M = ∅ then 1 else 0) := by
  by_cases hM : M = ∅
  · subst hM
    simp [Finset.powerset_empty]
  · have h := Finset.prod_add (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) M
    simp only [Finset.prod_const, mul_one, one_pow] at h
    have hne : M.Nonempty := Finset.nonempty_iff_ne_empty.mpr hM
    have hcard : M.card ≠ 0 := Finset.card_ne_zero.mpr hne
    have hbase : (-1 : ℝ) + 1 = 0 := by ring
    rw [hbase, zero_pow hcard] at h
    rw [ite_eq_right hM]
    exact h.symm

omit [Fintype Player] in
private theorem card_sdiff_of_subset {R T : Finset Player} (h : R ⊆ T) :
    (T \ R).card = T.card - R.card := by
  have h1 : R ∩ T = R := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · intro hx; exact hx.1
    · intro hx; exact ⟨hx, h hx⟩
  rw [Finset.card_sdiff, h1]

omit [Fintype Player] in
/-- Inner Möbius sum: summing the kernel over `T` with `R ⊆ T ⊆ S` picks out `R = S`. -/
private theorem inner_mobius_sum (S R : Finset Player) (hR : R ∈ S.powerset) :
    ∑ T ∈ S.powerset.filter (fun T => R ⊆ T), (-1 : ℝ) ^ (T.card - R.card)
      = (if R = S then 1 else 0) := by
  have hRS : R ⊆ S := Finset.mem_powerset.mp hR
  have hsum : ∑ T ∈ S.powerset.filter (fun T => R ⊆ T), (-1 : ℝ) ^ (T.card - R.card)
      = ∑ U ∈ (S \ R).powerset, (-1 : ℝ) ^ U.card := by
    apply Finset.sum_bij (fun T _ => T \ R)
    · intro T hT
      show T \ R ∈ (S \ R).powerset
      rw [Finset.mem_filter] at hT
      rw [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff (Finset.mem_powerset.mp hT.1) (fun _ h => h)
    · intro T₁ hT₁ T₂ hT₂ hEq
      rw [Finset.mem_filter] at hT₁ hT₂
      change T₁ \ R = T₂ \ R at hEq
      have e1 := Finset.sdiff_union_of_subset hT₁.2
      have e2 := Finset.sdiff_union_of_subset hT₂.2
      rw [← e1, ← e2, hEq]
    · intro U hU
      rw [Finset.mem_powerset] at hU
      refine ⟨U ∪ R, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_powerset]
        constructor
        · exact Finset.union_subset (fun x hx => Finset.sdiff_subset (hU hx)) hRS
        · exact Finset.subset_union_right
      · show (U ∪ R) \ R = U
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        have hxR : x ∈ U → x ∉ R := by
          intro hxU
          have hxSR := hU hxU
          rw [Finset.mem_sdiff] at hxSR
          exact hxSR.2
        constructor
        · rintro ⟨hU | hR, hnR⟩
          · exact hU
          · exact absurd hR hnR
        · intro hxU
          exact ⟨Or.inl hxU, hxR hxU⟩
    · intro T hT
      rw [Finset.mem_filter] at hT
      show (-1 : ℝ) ^ (T.card - R.card) = (-1 : ℝ) ^ (T \ R).card
      rw [card_sdiff_of_subset hT.2]
  rw [hsum, sum_powerset_neg_one_pow_card]
  have hiff : (S \ R = ∅) ↔ (R = S) := by
    constructor
    · intro h
      exact subset_antisymm hRS (Finset.sdiff_eq_empty_iff_subset.mp h)
    · intro h
      subst h
      exact Finset.sdiff_self R
  simp only [hiff]

omit [DecidableEq Player] [Fintype Player] in
/-- Möbius inversion on the subset lattice. -/
private theorem mobius_inversion (v : CoopGame Player) (S : Finset Player) :
    v.charFun ↑S = ∑ T ∈ S.powerset, mobiusCoeff v T := by
  classical
  have hTeq : ∀ T ∈ S.powerset, T.powerset = S.powerset.filter (fun R => R ⊆ T) := by
    intro T hT
    have hTS : T ⊆ S := Finset.mem_powerset.mp hT
    ext R
    simp only [Finset.mem_powerset, Finset.mem_filter]
    constructor
    · intro hRT; exact ⟨fun x hx => hTS (hRT hx), hRT⟩
    · intro h; exact h.2
  have hexpand : ∀ T ∈ S.powerset, mobiusCoeff v T
      = ∑ R ∈ S.powerset,
        (if R ⊆ T then (-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R else 0) := by
    intro T hT
    unfold mobiusCoeff
    rw [hTeq T hT, Finset.sum_filter]
  have hinner : ∀ R ∈ S.powerset, (∑ T ∈ S.powerset,
        (if R ⊆ T then (-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R else 0))
        = (if R = S then (1 : ℝ) else 0) * v.charFun ↑R := by
    intro R hR
    rw [← Finset.sum_filter, ← Finset.sum_mul, inner_mobius_sum S R hR]
  have hfinal : (∑ R ∈ S.powerset, (if R = S then (1 : ℝ) else 0) * v.charFun ↑R)
      = v.charFun ↑S := by
    have hterm : ∀ R ∈ S.powerset, ((if R = S then (1 : ℝ) else 0) * v.charFun ↑R)
        = (if R = S then v.charFun ↑R else 0) := by
      intro R _
      by_cases h : R = S
      · subst h; simp
      · simp [h]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    rw [ite_eq_left (Finset.mem_powerset.mpr (fun _ h => h))]
  symm
  calc ∑ T ∈ S.powerset, mobiusCoeff v T
      = ∑ T ∈ S.powerset, ∑ R ∈ S.powerset,
        (if R ⊆ T then (-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R else 0) :=
        Finset.sum_congr rfl hexpand
    _ = ∑ R ∈ S.powerset, ∑ T ∈ S.powerset,
        (if R ⊆ T then (-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R else 0) :=
        Finset.sum_comm
    _ = ∑ R ∈ S.powerset, ((if R = S then (1 : ℝ) else 0) * v.charFun ↑R) :=
        Finset.sum_congr rfl hinner
    _ = v.charFun ↑S := hfinal

/-- Every game is a combination of unanimity games with Möbius coefficients. -/
private theorem game_expansion (v : CoopGame Player) :
    v = ∑ T ∈ Finset.univ.powerset.filter (fun T => T ≠ ∅),
      mobiusCoeff v T • unanimity T := by
  classical
  ext S
  have hF : ∀ T ∈ Finset.univ.powerset.filter (fun T => T ≠ ∅),
      (mobiusCoeff v T • unanimity T).charFun S
      = (if (T : Set Player) ⊆ S then mobiusCoeff v T else 0) := by
    intro T hT
    rw [Finset.mem_filter] at hT
    rw [charFun_smul, unanimity_charFun hT.2]
    by_cases h : (T : Set Player) ⊆ S <;> simp [h]
  rw [charFun_sum, Finset.sum_congr rfl hF, ← Finset.sum_filter]
  have hsub_iff : ∀ T : Finset Player, T ⊆ S.toFinset ↔ (T : Set Player) ⊆ S := by
    intro T
    have hcoe : ((S.toFinset : Finset Player) : Set Player) = S := Set.coe_toFinset S
    have h := Finset.coe_subset (s₁ := T) (s₂ := S.toFinset)
    rw [hcoe] at h
    exact h.symm
  have hset : (Finset.univ.powerset.filter (fun T => T ≠ ∅)).filter
        (fun T : Finset Player => (T : Set Player) ⊆ S)
      = S.toFinset.powerset.filter (fun T => T ≠ ∅) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨-, hne⟩, hsub⟩
      exact ⟨(hsub_iff T).mpr hsub, hne⟩
    · rintro ⟨hsub, hne⟩
      exact ⟨⟨Finset.subset_univ T, hne⟩, (hsub_iff T).mp hsub⟩
  rw [hset]
  have hinv := mobius_inversion v S.toFinset
  rw [Set.coe_toFinset] at hinv
  rw [hinv]
  have hsub0 : S.toFinset.powerset.filter (fun T => T ≠ ∅) ⊆ S.toFinset.powerset :=
    Finset.filter_subset _ _
  have hzero : ∀ T ∈ S.toFinset.powerset,
      T ∉ S.toFinset.powerset.filter (fun T => T ≠ ∅) → mobiusCoeff v T = 0 := by
    intro T hT hnT
    have hTeq : T = ∅ := by
      by_contra hne
      rw [Finset.mem_filter] at hnT
      exact hnT ⟨hT, hne⟩
    subst hTeq
    exact mobiusCoeff_empty v
  exact (Finset.sum_subset hsub0 hzero).symm

omit [Fintype Player] in
private theorem unanimity_null_of_not_mem {T : Finset Player} (hT : T ≠ ∅) {i : Player}
    (hi : i ∉ T) : IsNullPlayer (unanimity T) i := by
  classical
  intro S _
  rw [unanimity_charFun hT, unanimity_charFun hT]
  have hiff : ((T : Set Player) ⊆ insert i S) ↔ ((T : Set Player) ⊆ S) := by
    constructor
    · intro h t ht
      have htT : t ∈ T := Finset.mem_coe.mp ht
      have hne : t ≠ i := fun heq => hi (heq ▸ htT)
      have hmem := h ht
      simp only [Set.mem_insert_iff] at hmem
      cases hmem with
      | inl heq => exact absurd heq hne
      | inr hm => exact hm
    · intro h t ht
      exact Set.mem_insert_of_mem i (h ht)
  rw [hiff]

omit [Fintype Player] in
private theorem unanimity_swap_invariant {T : Finset Player} (hT : T ≠ ∅) {i j : Player}
    (hi : i ∈ T) (hj : j ∈ T) (S : Set Player) :
    (unanimity T).charFun ((Equiv.swap i j) '' S) = (unanimity T).charFun S := by
  classical
  rw [unanimity_charFun hT, unanimity_charFun hT]
  have hpres : ∀ t : Player, t ∈ T → (Equiv.swap i j) t ∈ T := by
    intro t ht
    by_cases hti : t = i
    · subst hti
      rw [Equiv.swap_apply_left]
      exact hj
    · by_cases htj : t = j
      · subst htj
        rw [Equiv.swap_apply_right]
        exact hi
      · rw [Equiv.swap_apply_of_ne_of_ne hti htj]
        exact ht
  have hpres_symm : ∀ t : Player, t ∈ T → (Equiv.swap i j).symm t ∈ T := by
    intro t ht
    rw [Equiv.symm_swap]
    exact hpres t ht
  have hiff : ((T : Set Player) ⊆ (Equiv.swap i j) '' S) ↔ ((T : Set Player) ⊆ S) := by
    constructor
    · intro h t ht
      have htT : t ∈ T := Finset.mem_coe.mp ht
      have hst : (Equiv.swap i j) t ∈ (T : Set Player) :=
        Finset.mem_coe.mpr (hpres t htT)
      obtain ⟨s, hs, hσ⟩ := h hst
      have heq : s = t := Equiv.injective (Equiv.swap i j) hσ
      subst heq
      exact hs
    · intro h t ht
      have htT : t ∈ T := Finset.mem_coe.mp ht
      have hsymT : (Equiv.swap i j).symm t ∈ T := hpres_symm t htT
      have hsS : (Equiv.swap i j).symm t ∈ S := h (Finset.mem_coe.mpr hsymT)
      exact ⟨(Equiv.swap i j).symm t, hsS, Equiv.apply_symm_apply _ _⟩
  rw [hiff]

private theorem forced_unanimity (φ : CoopGame Player →ₗ[ℝ] (Player → ℝ))
    (heff : IsEfficient φ) (hsymm : IsSymmetric φ)
    (hnull : SatisfiesNullPlayerAxiom φ)
    (T : Finset Player) (hT : T ≠ ∅) (i : Player) :
    φ (unanimity T) i = if i ∈ T then 1 / (T.card : ℝ) else 0 := by
  classical
  have hnull_all : ∀ j : Player, j ∉ T → φ (unanimity T) j = 0 := by
    intro j hj
    exact hnull _ j (unanimity_null_of_not_mem hT hj)
  have hsym_all : ∀ a b : Player, a ∈ T → b ∈ T →
      φ (unanimity T) a = φ (unanimity T) b := by
    intro a b ha hb
    have hinv : ∀ S : Set Player,
        (unanimity T).charFun ((Equiv.swap a b) '' S) = (unanimity T).charFun S :=
      fun S => unanimity_swap_invariant hT ha hb S
    have hswap := hsymm (Equiv.swap a b) (unanimity T) hinv a
    rw [Equiv.swap_apply_left] at hswap
    exact hswap.symm
  have heff_one : ∑ j : Player, φ (unanimity T) j = 1 := by
    have he := heff (unanimity T)
    have hsub : ((T : Set Player) ⊆ Set.univ) := Set.subset_univ _
    have hchar : (unanimity T).charFun Set.univ = 1 := by
      rw [unanimity_charFun hT]
      simp [hsub]
    rw [hchar] at he
    exact he
  obtain ⟨j0, hj0⟩ := Finset.nonempty_iff_ne_empty.mpr hT
  have hcard_ne0 : T.card ≠ 0 := Finset.card_ne_zero.mpr ⟨j0, hj0⟩
  have hsum_T : ∑ j ∈ T, φ (unanimity T) j = 1 := by
    have hsub : T ⊆ Finset.univ := Finset.subset_univ T
    have hzero : ∀ x : Player, x ∈ Finset.univ → x ∉ T → φ (unanimity T) x = 0 :=
      fun x _ hx => hnull_all x hx
    have h := Finset.sum_subset hsub hzero
    have huniv : (∑ x ∈ Finset.univ, φ (unanimity T) x) = 1 := heff_one
    rw [huniv] at h
    exact h
  have hconst : ∀ j : Player, j ∈ T → φ (unanimity T) j = φ (unanimity T) j0 :=
    fun j hj => hsym_all j j0 hj hj0
  have hsum_const : (∑ j ∈ T, φ (unanimity T) j)
      = (T.card : ℝ) * φ (unanimity T) j0 := by
    have h1 : (∑ j ∈ T, φ (unanimity T) j)
        = ∑ _j ∈ T, φ (unanimity T) j0 := Finset.sum_congr rfl hconst
    rw [h1, Finset.sum_const, nsmul_eq_mul]
  have hmul : (T.card : ℝ) * φ (unanimity T) j0 = 1 := by
    rw [← hsum_const, hsum_T]
  have hj0_eq : φ (unanimity T) j0 = 1 / (T.card : ℝ) := by
    have hmul' : φ (unanimity T) j0 * (T.card : ℝ) = 1 := by
      rw [mul_comm]
      exact hmul
    exact eq_one_div_of_mul_eq_one_left hmul'
  by_cases hiT : i ∈ T
  · have hi_eq : φ (unanimity T) i = φ (unanimity T) j0 :=
      hsym_all i j0 hiT hj0
    rw [hi_eq, hj0_eq, ite_eq_left hiT]
  · rw [hnull_all i hiT, ite_eq_right hiT]

private theorem agree_on_unanimity (φ₁ φ₂ : CoopGame Player →ₗ[ℝ] (Player → ℝ))
    (h1e : IsEfficient φ₁) (h1s : IsSymmetric φ₁)
    (h1n : SatisfiesNullPlayerAxiom φ₁)
    (h2e : IsEfficient φ₂) (h2s : IsSymmetric φ₂)
    (h2n : SatisfiesNullPlayerAxiom φ₂)
    (T : Finset Player) : φ₁ (unanimity T) = φ₂ (unanimity T) := by
  funext i
  by_cases hT : T = ∅
  · subst hT
    rw [unanimity_zero, map_zero, map_zero]
  · rw [forced_unanimity φ₁ h1e h1s h1n T hT i,
        forced_unanimity φ₂ h2e h2s h2n T hT i]

omit [DecidableEq Player] in
private theorem shapley_uniqueness (φ₁ φ₂ : CoopGame Player →ₗ[ℝ] (Player → ℝ))
    (h1e : IsEfficient φ₁) (h1s : IsSymmetric φ₁)
    (h1n : SatisfiesNullPlayerAxiom φ₁)
    (h2e : IsEfficient φ₂) (h2s : IsSymmetric φ₂)
    (h2n : SatisfiesNullPlayerAxiom φ₂) :
    φ₁ = φ₂ := by
  apply LinearMap.ext
  intro v
  rw [game_expansion v, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [map_smul, map_smul]
  have hagree := agree_on_unanimity φ₁ φ₂ h1e h1s h1n h2e h2s h2n T
  rw [hagree]

omit [DecidableEq Player] [Fintype Player] in
private theorem mobiusCoeff_add (v w : CoopGame Player) (T : Finset Player) :
    mobiusCoeff (v + w) T = mobiusCoeff v T + mobiusCoeff w T := by
  unfold mobiusCoeff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R _
  rw [charFun_add, mul_add]

omit [DecidableEq Player] [Fintype Player] in
private theorem mobiusCoeff_smul (c : ℝ) (v : CoopGame Player) (T : Finset Player) :
    mobiusCoeff (c • v) T = c * mobiusCoeff v T := by
  unfold mobiusCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R _
  rw [charFun_smul]
  ring

private noncomputable def shapleyLM : CoopGame Player →ₗ[ℝ] (Player → ℝ) where
  toFun v := fun i =>
    ∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
      mobiusCoeff v T / (T.card : ℝ)
  map_add' v w := by
    funext i
    change (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff (v + w) T / (T.card : ℝ))
        = (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff v T / (T.card : ℝ))
        + (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff w T / (T.card : ℝ))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    rw [mobiusCoeff_add, add_div]
  map_smul' c v := by
    funext i
    change (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff (c • v) T / (T.card : ℝ))
        = c • (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff v T / (T.card : ℝ))
    rw [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [mobiusCoeff_smul, mul_div_assoc]

private theorem shapleyLM_apply (v : CoopGame Player) (i : Player) :
    shapleyLM v i = ∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
      mobiusCoeff v T / (T.card : ℝ) :=
  rfl

private theorem shapley_inner_sum (v : CoopGame Player) (T : Finset Player) :
    (∑ i ∈ Finset.univ, (if i ∈ T then mobiusCoeff v T / (T.card : ℝ) else 0))
      = mobiusCoeff v T := by
  by_cases hT : T = ∅
  · subst hT
    have hzero : ∀ i ∈ Finset.univ,
        (if i ∈ (∅ : Finset Player) then
          mobiusCoeff v ∅ / ((∅ : Finset Player).card : ℝ) else 0) = 0 := by
      intro i _
      simp
    rw [Finset.sum_congr rfl hzero]
    rw [Finset.sum_const_zero, mobiusCoeff_empty]
  · have hcard_ne : (T.card : ℝ) ≠ 0 := by
      have hne : T.card ≠ 0 :=
        Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
      exact Nat.cast_ne_zero.mpr hne
    have hfilter : Finset.univ.filter (fun i => i ∈ T) = T := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hrewrite :
        (∑ i ∈ Finset.univ, (if i ∈ T then mobiusCoeff v T / (T.card : ℝ) else 0))
        = ∑ _i ∈ T, mobiusCoeff v T / (T.card : ℝ) := by
      rw [← Finset.sum_filter, hfilter]
    rw [hrewrite, Finset.sum_const, nsmul_eq_mul]
    exact mul_div_cancel₀ _ hcard_ne

private theorem shapley_efficient :
    IsEfficient (shapleyLM : CoopGame Player →ₗ[ℝ] (Player → ℝ)) := by
  intro v
  show (∑ i : Player, shapleyLM v i) = v.charFun Set.univ
  have hstep1 : (∑ i : Player, shapleyLM v i)
      = ∑ i ∈ Finset.univ, ∑ T ∈ Finset.univ.powerset,
        (if i ∈ T then mobiusCoeff v T / (T.card : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [shapleyLM_apply]
    exact Finset.sum_filter _ _
  have hstep2 : (∑ i ∈ Finset.univ, ∑ T ∈ Finset.univ.powerset,
        (if i ∈ T then mobiusCoeff v T / (T.card : ℝ) else 0))
      = ∑ T ∈ Finset.univ.powerset, ∑ i ∈ Finset.univ,
        (if i ∈ T then mobiusCoeff v T / (T.card : ℝ) else 0) :=
    Finset.sum_comm
  have hstep3 : (∑ T ∈ Finset.univ.powerset, ∑ i ∈ Finset.univ,
        (if i ∈ T then mobiusCoeff v T / (T.card : ℝ) else 0))
      = ∑ T ∈ Finset.univ.powerset, mobiusCoeff v T := by
    apply Finset.sum_congr rfl
    intro T _
    exact shapley_inner_sum v T
  have hstep4 : (∑ T ∈ Finset.univ.powerset, mobiusCoeff v T)
      = v.charFun Set.univ := by
    have hinv := mobius_inversion v Finset.univ
    rw [Finset.coe_univ] at hinv
    exact hinv.symm
  rw [hstep1, hstep2, hstep3, hstep4]

omit [DecidableEq Player] [Fintype Player] in
private theorem mobiusCoeff_eq_zero_of_null (v : CoopGame Player) (i : Player)
    (hnull : IsNullPlayer v i) (T : Finset Player) (hiT : i ∈ T) :
    mobiusCoeff v T = 0 := by
  classical
  have hterm : ∀ R ∈ T.powerset.filter (fun R => i ∉ R),
      (-1 : ℝ) ^ (T.card - (insert i R).card) * v.charFun ↑(insert i R)
      = -((-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R) := by
    intro R hR
    rw [Finset.mem_filter] at hR
    have hRT : R ⊆ T := Finset.mem_powerset.mp hR.1
    have hiR : i ∉ R := hR.2
    have hcard : (insert i R).card = R.card + 1 :=
      Finset.card_insert_of_notMem hiR
    have hne : R ≠ T := by
      intro heq
      subst heq
      exact hiR hiT
    have hlt : R.card < T.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hRT, hne⟩)
    have hle : 1 ≤ T.card - R.card := by omega
    have hexp2 : T.card - (insert i R).card = T.card - R.card - 1 := by
      rw [hcard]
      omega
    have hchar : v.charFun ↑(insert i R) = v.charFun ↑R := by
      rw [Finset.coe_insert]
      have hiS : i ∉ (↑R : Set Player) := fun h => hiR (Finset.mem_coe.mp h)
      exact hnull ↑R hiS
    have hpow : (-1 : ℝ) ^ (T.card - (insert i R).card)
        = -(-1 : ℝ) ^ (T.card - R.card) := by
      rw [hexp2]
      have hm : T.card - R.card - 1 + 1 = T.card - R.card :=
        Nat.sub_add_cancel hle
      have hpow_eq : (-1 : ℝ) ^ (T.card - R.card)
          = (-1 : ℝ) ^ (T.card - R.card - 1) * (-1) := by
        conv_lhs => rw [← hm, pow_succ]
      have hneg : (-1 : ℝ) ^ (T.card - R.card - 1) * (-1)
          = -(-1 : ℝ) ^ (T.card - R.card - 1) := by ring
      rw [hneg] at hpow_eq
      have h2 := congrArg (fun x : ℝ => -x) hpow_eq
      simp only [neg_neg] at h2
      exact h2.symm
    rw [hchar, hpow]
    ring
  have hreindex : (∑ R ∈ T.powerset.filter (fun R => i ∉ R),
        (-1 : ℝ) ^ (T.card - (insert i R).card) * v.charFun ↑(insert i R))
      = ∑ R' ∈ T.powerset.filter (fun R' => i ∈ R'),
        (-1 : ℝ) ^ (T.card - R'.card) * v.charFun ↑R' := by
    apply Finset.sum_bij (fun R _ => insert i R)
    · intro R hR
      rw [Finset.mem_filter] at hR ⊢
      have hRT : R ⊆ T := Finset.mem_powerset.mp hR.1
      constructor
      · rw [Finset.mem_powerset]
        rw [Finset.insert_subset_iff]
        exact ⟨hiT, hRT⟩
      · exact Finset.mem_insert_self i R
    · intro R₁ hR₁ R₂ hR₂ hEq
      rw [Finset.mem_filter] at hR₁ hR₂
      have e1 := Finset.erase_insert hR₁.2
      have e2 := Finset.erase_insert hR₂.2
      have h := congrArg (fun S => S.erase i) hEq
      rw [e1, e2] at h
      exact h
    · intro R' hR'
      rw [Finset.mem_filter] at hR'
      have hRT' : R' ⊆ T := Finset.mem_powerset.mp hR'.1
      have hiR' : i ∈ R' := hR'.2
      refine ⟨R'.erase i, ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_powerset]
          exact (Finset.erase_subset i R').trans hRT'
        · exact Finset.notMem_erase i R'
      · exact Finset.insert_erase hiR'
    · intro R _
      rfl
  have hsum_eq : (∑ R' ∈ T.powerset.filter (fun R' => i ∈ R'),
        (-1 : ℝ) ^ (T.card - R'.card) * v.charFun ↑R')
      = ∑ R ∈ T.powerset.filter (fun R => i ∉ R),
        -((-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R) := by
    rw [← hreindex]
    apply Finset.sum_congr rfl
    intro R hR
    exact hterm R hR
  have hneg : (∑ R' ∈ T.powerset.filter (fun R' => i ∈ R'),
        (-1 : ℝ) ^ (T.card - R'.card) * v.charFun ↑R')
      = -(∑ R ∈ T.powerset.filter (fun R => i ∉ R),
        (-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R) := by
    rw [hsum_eq]
    exact Finset.sum_neg_distrib _
  unfold mobiusCoeff
  have hsplit := Finset.sum_filter_add_sum_filter_not T.powerset
    (fun R => i ∈ R)
    (fun R => (-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R)
  rw [← hsplit, hneg]
  exact neg_add_cancel _

private theorem shapley_null : SatisfiesNullPlayerAxiom
    (shapleyLM : CoopGame Player →ₗ[ℝ] (Player → ℝ)) := by
  intro v i hnull
  rw [shapleyLM_apply]
  apply Finset.sum_eq_zero
  intro T hT
  rw [Finset.mem_filter] at hT
  have hcz : mobiusCoeff v T = 0 :=
    mobiusCoeff_eq_zero_of_null v i hnull T hT.2
  rw [hcz, zero_div]

omit [Fintype Player] in
private theorem mobiusCoeff_perm (σ : Equiv.Perm Player) (v : CoopGame Player)
    (hinv : ∀ S : Set Player, v.charFun (σ '' S) = v.charFun S)
    (T : Finset Player) :
    mobiusCoeff v (Finset.image (⇑σ) T) = mobiusCoeff v T := by
  unfold mobiusCoeff
  have hinj : Function.Injective (⇑σ) := Equiv.injective σ
  have hcardT : (Finset.image (⇑σ) T).card = T.card :=
    Finset.card_image_of_injective T hinj
  have hpowerset : (Finset.image (⇑σ) T).powerset
      = Finset.image (fun R => Finset.image (⇑σ) R) T.powerset :=
    Finset.powerset_image
  rw [hpowerset]
  have hinjOn : Set.InjOn (fun R => Finset.image (⇑σ) R) ↑(T.powerset) := by
    apply Set.injOn_of_injective
    exact Finset.image_injective hinj
  rw [Finset.sum_image hinjOn]
  apply Finset.sum_congr rfl
  intro R _
  have hcardR : (Finset.image (⇑σ) R).card = R.card :=
    Finset.card_image_of_injective R hinj
  have hchar : v.charFun ↑(Finset.image (⇑σ) R) = v.charFun ↑R := by
    rw [Finset.coe_image]
    exact hinv ↑R
  rw [hcardT, hcardR, hchar]

private theorem image_univ_perm (σ : Equiv.Perm Player) :
    Finset.image (⇑σ) Finset.univ = Finset.univ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨σ.symm x, Equiv.apply_symm_apply σ x⟩

private theorem shapley_symmetric : IsSymmetric
    (shapleyLM : CoopGame Player →ₗ[ℝ] (Player → ℝ)) := by
  intro σ v hinv i
  rw [shapleyLM_apply, shapleyLM_apply, Finset.sum_filter, Finset.sum_filter]
  have hinj : Function.Injective (⇑σ) := Equiv.injective σ
  have hpowerset_image : (Finset.univ : Finset Player).powerset
      = Finset.image (fun T => Finset.image (⇑σ) T)
        (Finset.univ : Finset Player).powerset := by
    have himg : Finset.image (⇑σ) (Finset.univ : Finset Player) = Finset.univ :=
      image_univ_perm σ
    have h := Finset.powerset_image (s := (Finset.univ : Finset Player)) (f := (⇑σ))
    rw [himg] at h
    exact h
  have hinjOn : Set.InjOn (fun T => Finset.image (⇑σ) T)
      ↑((Finset.univ : Finset Player).powerset) := by
    apply Set.injOn_of_injective
    exact Finset.image_injective hinj
  conv_lhs => rw [hpowerset_image, Finset.sum_image hinjOn]
  apply Finset.sum_congr rfl
  intro T _
  have hmem : (σ i ∈ Finset.image (⇑σ) T) ↔ (i ∈ T) := by
    constructor
    · intro h
      rw [Finset.mem_image] at h
      obtain ⟨a, haT, haeq⟩ := h
      have heq : a = i := hinj haeq
      subst heq
      exact haT
    · intro h
      rw [Finset.mem_image]
      exact ⟨i, h, rfl⟩
  have hcard : (Finset.image (⇑σ) T).card = T.card :=
    Finset.card_image_of_injective T hinj
  have hmob : mobiusCoeff v (Finset.image (⇑σ) T) = mobiusCoeff v T :=
    mobiusCoeff_perm σ v hinv T
  by_cases hi : i ∈ T
  · have hσmem : σ i ∈ Finset.image (⇑σ) T := hmem.mpr hi
    rw [ite_eq_left hσmem, ite_eq_left hi, hmob, hcard]
  · have hσnmem : σ i ∉ Finset.image (⇑σ) T := fun h => hi (hmem.mp h)
    rw [ite_eq_right hσnmem, ite_eq_right hi]

omit [DecidableEq Player] in
public theorem shapley_characterization : ∃! φ : CoopGame Player →ₗ[ℝ] (Player → ℝ),
    IsEfficient φ ∧ IsSymmetric φ ∧ SatisfiesNullPlayerAxiom φ := by
  refine ExistsUnique.intro shapleyLM
    ⟨shapley_efficient, shapley_symmetric, shapley_null⟩ ?_
  intro φ hφ
  obtain ⟨he, hs, hn⟩ := hφ
  exact shapley_uniqueness φ shapleyLM he hs hn
    shapley_efficient shapley_symmetric shapley_null

end MathlibExt.GameTheory.ShapleyValue
