/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FK.InhomogeneousFKG
import Code.FK.RussoDerivativeBetaSum
import Code.FK.FiniteEnergy

open scoped BigOperators
open Finset

namespace StatMech
namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



noncomputable def extendActive (ω : ConfigSpace G.edgeSet) : ConfigSpace (Sym2 V) :=
  fun e => if h : e ∈ G.edgeSet then ω ⟨e, h⟩ else false

@[simp] theorem extendActive_apply (ω : ConfigSpace G.edgeSet) (e : G.edgeSet) :
    extendActive G ω e.1 = ω e := by
  simp [extendActive, e.2]

theorem extendActive_sup (ω η : ConfigSpace G.edgeSet) :
    extendActive G (ω ⊔ η) = extendActive G ω ⊔ extendActive G η := by
  funext e
  by_cases he : e ∈ G.edgeSet <;> simp [extendActive, he]

theorem extendActive_inf (ω η : ConfigSpace G.edgeSet) :
    extendActive G (ω ⊓ η) = extendActive G ω ⊓ extendActive G η := by
  funext e
  by_cases he : e ∈ G.edgeSet <;> simp [extendActive, he]

theorem extendActive_setOpen (e : G.edgeSet) (ω : ConfigSpace G.edgeSet) :
    extendActive G (setOpen e ω) = setOpen e.1 (extendActive G ω) := by
  funext a
  by_cases ha : a = e.1
  · subst a
    simp [extendActive, e.2]
  · by_cases hG : a ∈ G.edgeSet
    · have hne : (⟨a, hG⟩ : G.edgeSet) ≠ e := by
        intro h
        exact ha (congrArg Subtype.val h)
      rw [setOpen_of_ne ha]
      simp [extendActive, hG, setOpen_of_ne hne]
    · simp [extendActive, hG, setOpen_of_ne ha]

theorem extendActive_setClosed (e : G.edgeSet) (ω : ConfigSpace G.edgeSet) :
    extendActive G (setClosed e ω) = setClosed e.1 (extendActive G ω) := by
  funext a
  by_cases ha : a = e.1
  · subst a
    simp [extendActive, e.2]
  · by_cases hG : a ∈ G.edgeSet
    · have hne : (⟨a, hG⟩ : G.edgeSet) ≠ e := by
        intro h
        exact ha (congrArg Subtype.val h)
      rw [setClosed_of_ne ha]
      simp [extendActive, hG, setClosed_of_ne hne]
    · simp [extendActive, hG, setClosed_of_ne ha]


noncomputable def activeWeight (pf : Sym2 V → ℝ) (q : ℝ)
    (ω : ConfigSpace G.edgeSet) : ℝ :=
  fkWeightW G pf q (extendActive G ω)


noncomputable def activeZ (pf : Sym2 V → ℝ) (q : ℝ) : ℝ :=
  ∑ ω : ConfigSpace G.edgeSet, activeWeight G pf q ω


noncomputable def activeProb (pf : Sym2 V → ℝ) (q : ℝ)
    (ω : ConfigSpace G.edgeSet) : ℝ :=
  activeWeight G pf q ω / activeZ G pf q


noncomputable def activeMean (pf : Sym2 V → ℝ) (q : ℝ)
    (f : ConfigSpace G.edgeSet → ℝ) : ℝ :=
  ∑ ω, f ω * activeProb G pf q ω


noncomputable def activeCov (pf : Sym2 V → ℝ) (q : ℝ)
    (f g : ConfigSpace G.edgeSet → ℝ) : ℝ :=
  activeMean G pf q (fun ω => f ω * g ω) -
    activeMean G pf q f * activeMean G pf q g


noncomputable def activeNumer (pf : Sym2 V → ℝ) (q : ℝ)
    (f : ConfigSpace G.edgeSet → ℝ) : ℝ :=
  ∑ ω, f ω * activeWeight G pf q ω


noncomputable def activeBetaScore (J : Sym2 V → ℝ) (β : ℝ)
    (ω : ConfigSpace G.edgeSet) : ℝ :=
  ∑ e : G.edgeSet, (J e.1 / betaParams J β e.1) *
    (OSSS.Lindeberg.coord e ω - betaParams J β e.1)


noncomputable def activeProbOf (pf : Sym2 V → ℝ) (q : ℝ)
    (A : Set (ConfigSpace G.edgeSet)) : ℝ :=
  activeMean G pf q (A.indicator (fun _ => (1 : ℝ)))

theorem activeWeight_pos {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) (ω : ConfigSpace G.edgeSet) :
    0 < activeWeight G pf q ω :=
  fkWeightW_pos G hpf hpf1 hq (extendActive G ω)

theorem activeZ_pos {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) : 0 < activeZ G pf q := by
  unfold activeZ
  exact Finset.sum_pos' (fun ω _ => (activeWeight_pos G hpf hpf1 hq ω).le)
    ⟨fun _ => false, Finset.mem_univ _, activeWeight_pos G hpf hpf1 hq _⟩

theorem activeProb_pos {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) (ω : ConfigSpace G.edgeSet) :
    0 < activeProb G pf q ω := by
  exact div_pos (activeWeight_pos G hpf hpf1 hq ω) (activeZ_pos G hpf hpf1 hq)

theorem activeProb_sum_eq_one {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) :
    ∑ ω, activeProb G pf q ω = 1 := by
  unfold activeProb activeZ
  rw [← Finset.sum_div]
  exact div_self (activeZ_pos G hpf hpf1 hq).ne'

theorem activeWeight_logSupermodular {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) (ω η : ConfigSpace G.edgeSet) :
    activeWeight G pf q ω * activeWeight G pf q η ≤
      activeWeight G pf q (ω ⊔ η) * activeWeight G pf q (ω ⊓ η) := by
  unfold activeWeight
  rw [extendActive_sup, extendActive_inf]
  exact fkWeightW_logSupermodular G hpf hpf1 hq _ _

theorem activeProb_FKGLatticeCondition {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) :
    FKGLatticeCondition (activeProb G pf q) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hZ : 0 < activeZ G pf q := activeZ_pos G hpf hpf1 hq0
  intro ω η
  unfold activeProb
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZ hZ)).mpr
    (activeWeight_logSupermodular G hpf hpf1 hq ω η)

lemma edgeProductW_setOpen (pf : Sym2 V → ℝ) (e : G.edgeSet)
    (ω : ConfigSpace (Sym2 V)) :
    edgeProductW G pf (setOpen e.1 ω) =
      (∏ a ∈ G.edgeFinset.erase e.1, (if ω a then pf a else 1 - pf a)) * pf e.1 := by
  unfold edgeProductW
  have he : e.1 ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]
    exact e.2
  rw [← Finset.prod_erase_mul _ _ he]
  congr 1
  · apply Finset.prod_congr rfl
    intro a ha
    rw [setOpen_of_ne]
    exact (Finset.mem_erase.mp ha).1
  · simp [setOpen_self]

lemma edgeProductW_setClosed (pf : Sym2 V → ℝ) (e : G.edgeSet)
    (ω : ConfigSpace (Sym2 V)) :
    edgeProductW G pf (setClosed e.1 ω) =
      (∏ a ∈ G.edgeFinset.erase e.1, (if ω a then pf a else 1 - pf a)) *
        (1 - pf e.1) := by
  unfold edgeProductW
  have he : e.1 ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]
    exact e.2
  rw [← Finset.prod_erase_mul _ _ he]
  congr 1
  · apply Finset.prod_congr rfl
    intro a ha
    rw [setClosed_of_ne]
    exact (Finset.mem_erase.mp ha).1
  · simp [setClosed_self]


theorem activeWeight_close_pair {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) (e : G.edgeSet) (ω : ConfigSpace G.edgeSet) :
    (1 - pf e.1) * activeWeight G pf q (setOpen e ω) ≤
      pf e.1 * activeWeight G pf q (setClosed e ω) := by
  unfold activeWeight fkWeightW
  rw [extendActive_setOpen, extendActive_setClosed,
    edgeProductW_setOpen, edgeProductW_setClosed]
  let R := ∏ a ∈ G.edgeFinset.erase e.1,
    (if extendActive G ω a then pf a else 1 - pf a)
  have hR : 0 ≤ R := by
    unfold R
    apply Finset.prod_nonneg
    intro a _
    split
    · exact (hpf a).le
    · linarith [hpf1 a]
  have hpow : q ^ numClusters G (setOpen e.1 (extendActive G ω)) ≤
      q ^ numClusters G (setClosed e.1 (extendActive G ω)) :=
    pow_le_pow_right₀ hq (numClusters_setOpen_le G e.1 (extendActive G ω))
  have hp : 0 ≤ pf e.1 * (1 - pf e.1) := mul_nonneg (hpf _).le (by linarith [hpf1 e.1])
  nlinarith [mul_le_mul_of_nonneg_left hpow (mul_nonneg hR hp)]

section Fiber

variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def openMarginal (μ : ConfigSpace E → ℝ) (e : E) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace E => ω e = true), μ ω

lemma openMarginal_eq_closedFiber (μ : ConfigSpace E → ℝ) (e : E) :
    openMarginal μ e =
      ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace E => ψ e = false), μ (setOpen e ψ) := by
  unfold openMarginal
  apply Finset.sum_nbij' (fun ω => setClosed e ω) (fun ψ => setOpen e ψ)
  · intro ω _
    simp [setClosed]
  · intro ψ _
    simp [setOpen]
  · intro ω hω
    simp only [Finset.mem_filter] at hω
    funext x
    by_cases hx : x = e
    · subst hx
      simp [hω.2]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]
  · intro ψ hψ
    simp only [Finset.mem_filter] at hψ
    funext x
    by_cases hx : x = e
    · subst hx
      simp [hψ.2]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]
  · intro ω hω
    simp only [Finset.mem_filter] at hω
    congr 1
    funext x
    by_cases hx : x = e
    · subst hx
      simp [hω.2]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]

lemma activeClosedFiber_pairMass_eq_one (μ : ConfigSpace E → ℝ)
    (hμ1 : ∑ ω, μ ω = 1) (e : E) :
    ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace E => ψ e = false),
      (μ (setOpen e ψ) + μ (setClosed e ψ)) = 1 := by
  rw [Finset.sum_add_distrib, ← openMarginal_eq_closedFiber]
  have hclosed : (∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace E => ψ e = false),
      μ (setClosed e ψ)) =
      ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace E => ω e = false), μ ω := by
    apply Finset.sum_congr rfl
    intro ψ hψ
    simp only [Finset.mem_filter] at hψ
    congr 1
    funext x
    by_cases hx : x = e
    · subst hx
      simp [hψ.2]
    · simp [setClosed_of_ne hx]
  rw [hclosed]
  unfold openMarginal
  rw [show Finset.univ.filter (fun ω : ConfigSpace E => ω e = false) =
      Finset.univ.filter (fun ω : ConfigSpace E => ¬ ω e = true) by ext ω; simp]
  rw [Finset.sum_filter_add_sum_filter_not]
  exact hμ1

lemma openMarginal_le_of_close_pair (μ : ConfigSpace E → ℝ)
    (hμ1 : ∑ ω, μ ω = 1) (e : E) {p : ℝ}
    (hpair : ∀ ψ, (1 - p) * μ (setOpen e ψ) ≤ p * μ (setClosed e ψ)) :
    openMarginal μ e ≤ p := by
  let S := Finset.univ.filter (fun ψ : ConfigSpace E => ψ e = false)
  have hsum := Finset.sum_le_sum (fun ψ (_ : ψ ∈ S) => hpair ψ)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [← openMarginal_eq_closedFiber μ e] at hsum
  have hpair1 := activeClosedFiber_pairMass_eq_one μ hμ1 e
  change (∑ ψ ∈ S, (μ (setOpen e ψ) + μ (setClosed e ψ))) = 1 at hpair1
  rw [Finset.sum_add_distrib, ← openMarginal_eq_closedFiber μ e] at hpair1
  calc
    openMarginal μ e = (1 - p) * openMarginal μ e + p * openMarginal μ e := by ring
    _ ≤ p * (∑ ψ ∈ S, μ (setClosed e ψ)) + p * openMarginal μ e :=
      by simpa [add_comm] using add_le_add_right hsum (p * openMarginal μ e)
    _ = p := by rw [← mul_add, add_comm, hpair1, mul_one]

end Fiber

theorem active_openMarginal_le_param {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) (e : G.edgeSet) :
    openMarginal (activeProb G pf q) e ≤ pf e.1 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  apply openMarginal_le_of_close_pair _
    (activeProb_sum_eq_one G hpf hpf1 hq0) e
  intro ψ
  unfold activeProb
  have hZ : 0 < activeZ G pf q := activeZ_pos G hpf hpf1 hq0
  rw [show (1 - pf e.1) * (activeWeight G pf q (setOpen e ψ) / activeZ G pf q) =
      ((1 - pf e.1) * activeWeight G pf q (setOpen e ψ)) / activeZ G pf q by ring]
  rw [show pf e.1 * (activeWeight G pf q (setClosed e ψ) / activeZ G pf q) =
      (pf e.1 * activeWeight G pf q (setClosed e ψ)) / activeZ G pf q by ring]
  exact (div_le_div_iff_of_pos_right hZ).2
    (activeWeight_close_pair G hpf hpf1 hq e ψ)

section ClosedProduct

variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def closedProd (S : Finset E) (ω : ConfigSpace E) : ℝ :=
  ∏ e ∈ S, if ω e then 0 else 1

lemma closedProd_antitone (S : Finset E) : Antitone (closedProd S) := by
  intro ω η hωη
  unfold closedProd
  apply Finset.prod_le_prod
  · intro e he
    positivity
  · intro e he
    have h := hωη e
    cases hω : ω e <;> cases hη : η e <;>
      simp_all (config := { decide := true })
    have hn : ¬ ((true : Bool) ≤ false) := by decide
    exact False.elim (hn h)

lemma closedProd_insert {e : E} {S : Finset E} (he : e ∉ S)
    (ω : ConfigSpace E) :
    closedProd (insert e S) ω = closedProd S ω * closedProd {e} ω := by
  simp [closedProd, he, mul_comm]

lemma fkg_inequality_antitone {μ : ConfigSpace E → ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ)
    {f g : ConfigSpace E → ℝ} (hf : Antitone f) (hg : Antitone g) :
    (∑ ω, μ ω * f ω) * (∑ ω, μ ω * g ω) ≤
      ∑ ω, μ ω * (f ω * g ω) := by
  have hnf : Monotone (fun ω => -f ω) := by
    intro a b hab
    exact neg_le_neg (hf hab)
  have hng : Monotone (fun ω => -g ω) := by
    intro a b hab
    exact neg_le_neg (hg hab)
  have h := fkg_inequality hμ0 hμ1 hFKG hnf hng
  simpa only [mul_neg, Finset.sum_neg_distrib, neg_mul, neg_neg] using h

lemma mean_closedProd_singleton (μ : ConfigSpace E → ℝ)
    (hμ1 : ∑ ω, μ ω = 1) (e : E) :
    (∑ ω, μ ω * closedProd {e} ω) = 1 - openMarginal μ e := by
  have hopen : openMarginal μ e =
      ∑ ω, μ ω * (if ω e then (1 : ℝ) else 0) := by
    unfold openMarginal
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : ω e = true <;> simp [h]
  rw [hopen]
  unfold closedProd
  simp only [Finset.prod_singleton]
  calc
    (∑ ω, μ ω * if ω e then 0 else 1) =
        ∑ ω, (μ ω - μ ω * if ω e then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro ω _
      cases h : ω e <;> simp [h]
    _ = (∑ ω, μ ω) - ∑ ω, μ ω * (if ω e then 1 else 0) := by
      rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ ω, μ ω * (if ω e then 1 else 0) := by rw [hμ1]


theorem prod_one_sub_openMarginal_le_closedProd
    (μ : ConfigSpace E → ℝ) (hμ0 : 0 ≤ μ) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) (S : Finset E) :
    (∏ e ∈ S, (1 - openMarginal μ e)) ≤
      ∑ ω, μ ω * closedProd S ω := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [closedProd, hμ1]
  | @insert e S he ih =>
      rw [Finset.prod_insert he]
      have hsingle0 : 0 ≤ 1 - openMarginal μ e := by
        rw [← mean_closedProd_singleton μ hμ1 e]
        apply Finset.sum_nonneg
        intro ω _
        apply mul_nonneg (hμ0 ω)
        simp only [closedProd, Finset.prod_singleton]
        split <;> norm_num
      calc
        (1 - openMarginal μ e) * ∏ x ∈ S, (1 - openMarginal μ x)
            ≤ (1 - openMarginal μ e) *
                ∑ ω, μ ω * closedProd S ω :=
          mul_le_mul_of_nonneg_left ih hsingle0
        _ = (∑ ω, μ ω * closedProd S ω) *
              (∑ ω, μ ω * closedProd {e} ω) := by
          rw [mean_closedProd_singleton μ hμ1 e]
          ring
        _ ≤ ∑ ω, μ ω * (closedProd S ω * closedProd {e} ω) :=
          fkg_inequality_antitone hμ0 hμ1 hFKG
            (closedProd_antitone S) (closedProd_antitone {e})
        _ = ∑ ω, μ ω * closedProd (insert e S) ω := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [closedProd_insert he]

end ClosedProduct



theorem active_prod_closed_param_le {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 1 ≤ q) (S : Finset G.edgeSet) :
    (∏ e ∈ S, (1 - pf e.1)) ≤
      ∑ ω, activeProb G pf q ω * closedProd S ω := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hμ0 : 0 ≤ activeProb G pf q :=
    fun ω => (activeProb_pos G hpf hpf1 hq0 ω).le
  have hμ1 := activeProb_sum_eq_one G hpf hpf1 hq0
  have hFKG := activeProb_FKGLatticeCondition G hpf hpf1 hq
  refine (Finset.prod_le_prod (fun e he => by linarith [hpf1 e.1]) ?_).trans
    (prod_one_sub_openMarginal_le_closedProd _ hμ0 hμ1 hFKG S)
  intro e he
  linarith [active_openMarginal_le_param G hpf hpf1 hq e]

lemma betaScore_extendActive (J : Sym2 V → ℝ) (β : ℝ)
    (ω : ConfigSpace G.edgeSet) :
    betaScore G J β (extendActive G ω) = activeBetaScore G J β ω := by
  unfold betaScore activeBetaScore
  rw [Finset.sum_subtype G.edgeFinset]
  · apply Finset.sum_congr rfl
    intro e _
    congr 2
    simp [coordR, OSSS.Lindeberg.coord, extendActive_apply]
  · intro e
    rw [SimpleGraph.mem_edgeFinset]

theorem hasDerivAt_activeWeight_beta {J : Sym2 V → ℝ}
    (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β) (q : ℝ)
    (ω : ConfigSpace G.edgeSet) :
    HasDerivAt (fun b => activeWeight G (betaParams J b) q ω)
      (activeWeight G (betaParams J β) q ω * activeBetaScore G J β ω) β := by
  simpa [activeWeight, betaScore_extendActive] using
    hasDerivAt_fkWeightW_beta G hJ hβ q (extendActive G ω)

theorem hasDerivAt_activeNumer_beta {J : Sym2 V → ℝ}
    (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β) (q : ℝ)
    (f : ConfigSpace G.edgeSet → ℝ) :
    HasDerivAt (fun b => activeNumer G (betaParams J b) q f)
      (activeNumer G (betaParams J β) q (fun ω => f ω * activeBetaScore G J β ω)) β := by
  unfold activeNumer
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun ω _ => (hasDerivAt_activeWeight_beta G hJ hβ q ω).const_mul (f ω))
  refine hsum.congr_deriv ?_
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma activeNumer_one (pf : Sym2 V → ℝ) (q : ℝ) :
    activeNumer G pf q (fun _ => 1) = activeZ G pf q := by
  simp [activeNumer, activeZ]

lemma activeMean_eq_div (pf : Sym2 V → ℝ) (q : ℝ)
    (f : ConfigSpace G.edgeSet → ℝ) :
    activeMean G pf q f = activeNumer G pf q f / activeZ G pf q := by
  unfold activeMean activeNumer activeProb
  rw [show (fun ω => f ω * (activeWeight G pf q ω / activeZ G pf q)) =
      (fun ω => (f ω * activeWeight G pf q ω) / activeZ G pf q) by
    funext ω
    ring]
  rw [← Finset.sum_div]

lemma activeMean_add (pf : Sym2 V → ℝ) (q : ℝ)
    (f g : ConfigSpace G.edgeSet → ℝ) :
    activeMean G pf q (fun ω => f ω + g ω) =
      activeMean G pf q f + activeMean G pf q g := by
  unfold activeMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma activeMean_const_mul (pf : Sym2 V → ℝ) (q c : ℝ)
    (f : ConfigSpace G.edgeSet → ℝ) :
    activeMean G pf q (fun ω => c * f ω) = c * activeMean G pf q f := by
  unfold activeMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma activeMean_sum (pf : Sym2 V → ℝ) (q : ℝ)
    {ι : Type*} [Fintype ι] (g : ι → ConfigSpace G.edgeSet → ℝ) :
    activeMean G pf q (fun ω => ∑ i, g i ω) =
      ∑ i, activeMean G pf q (g i) := by
  classical
  unfold activeMean
  rw [← Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_mul]

lemma activeCov_const_mul_right (pf : Sym2 V → ℝ) (q c : ℝ)
    (f g : ConfigSpace G.edgeSet → ℝ) :
    activeCov G pf q f (fun ω => c * g ω) = c * activeCov G pf q f g := by
  unfold activeCov
  rw [activeMean_const_mul]
  have hprod : (fun ω => f ω * (c * g ω)) = (fun ω => c * (f ω * g ω)) := by
    funext ω
    ring
  rw [hprod, activeMean_const_mul]
  ring

lemma activeCov_sum_right (pf : Sym2 V → ℝ) (q : ℝ)
    (f : ConfigSpace G.edgeSet → ℝ) {ι : Type*} [Fintype ι]
    (g : ι → ConfigSpace G.edgeSet → ℝ) :
    activeCov G pf q f (fun ω => ∑ i, g i ω) =
      ∑ i, activeCov G pf q f (g i) := by
  classical
  unfold activeCov
  rw [show (fun ω => f ω * ∑ i, g i ω) =
      (fun ω => ∑ i, f ω * g i ω) by funext ω; rw [Finset.mul_sum]]
  rw [activeMean_sum, activeMean_sum]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]

lemma activeCov_sub_const {pf : Sym2 V → ℝ}
    (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) (f g : ConfigSpace G.edgeSet → ℝ) (c : ℝ) :
    activeCov G pf q f (fun ω => g ω - c) = activeCov G pf q f g := by
  have hone : activeMean G pf q (fun _ : ConfigSpace G.edgeSet => (1 : ℝ)) = 1 := by
    simpa [activeMean] using activeProb_sum_eq_one G hpf hpf1 hq
  unfold activeCov
  rw [show (fun ω => f ω * (g ω - c)) =
      (fun ω => f ω * g ω + (-c) * f ω) by funext ω; ring]
  rw [activeMean_add, activeMean_const_mul]
  rw [show (fun ω : ConfigSpace G.edgeSet => g ω - c) =
      (fun ω => g ω + (-c) * 1) by funext ω; ring]
  rw [activeMean_add, activeMean_const_mul, hone]
  ring

theorem hasDerivAt_activeMean_beta_sum {J : Sym2 V → ℝ}
    (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β)
    {q : ℝ} (hq : 0 < q) (f : ConfigSpace G.edgeSet → ℝ) :
    HasDerivAt (fun b => activeMean G (betaParams J b) q f)
      (∑ e : G.edgeSet, (J e.1 / betaParams J β e.1) *
        activeCov G (betaParams J β) q f (OSSS.Lindeberg.coord e)) β := by
  have hN := hasDerivAt_activeNumer_beta G hJ hβ q f
  have hZraw := hasDerivAt_activeNumer_beta G hJ hβ q (fun _ => 1)
  have hZ : HasDerivAt (fun b => activeZ G (betaParams J b) q)
      (activeNumer G (betaParams J β) q (activeBetaScore G J β)) β := by
    simpa only [activeNumer_one, one_mul] using hZraw
  have hZne : activeZ G (betaParams J β) q ≠ 0 :=
    (activeZ_pos G (betaParams_pos hJ hβ) (betaParams_lt_one J β) hq).ne'
  rw [show (fun b => activeMean G (betaParams J b) q f) =
      (fun b => activeNumer G (betaParams J b) q f /
        activeZ G (betaParams J b) q) by
    funext b
    exact activeMean_eq_div G _ _ _]
  refine (hN.div hZ hZne).congr_deriv ?_
  have hscore : activeCov G (betaParams J β) q f (activeBetaScore G J β) =
      ∑ e : G.edgeSet, (J e.1 / betaParams J β e.1) *
        activeCov G (betaParams J β) q f (OSSS.Lindeberg.coord e) := by
    unfold activeBetaScore
    rw [activeCov_sum_right]
    apply Finset.sum_congr rfl
    intro e _
    rw [activeCov_const_mul_right]
    rw [activeCov_sub_const G (betaParams_pos hJ hβ)
      (betaParams_lt_one J β) hq]
  rw [← hscore]
  unfold activeCov
  rw [activeMean_eq_div, activeMean_eq_div, activeMean_eq_div]
  field_simp

theorem hasDerivAt_activeProbOf_beta_sum {J : Sym2 V → ℝ}
    (hJ : ∀ e, 0 < J e) {β : ℝ} (hβ : 0 < β)
    {q : ℝ} (hq : 0 < q) (A : Set (ConfigSpace G.edgeSet)) :
    HasDerivAt (fun b => activeProbOf G (betaParams J b) q A)
      (∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(β * J e.1)))) *
        activeCov G (betaParams J β) q (A.indicator (fun _ => (1 : ℝ)))
          (OSSS.Lindeberg.coord e)) β := by
  simpa [activeProbOf, betaParams] using
    hasDerivAt_activeMean_beta_sum G hJ hβ hq (A.indicator (fun _ => (1 : ℝ)))

end FK
end StatMech
