/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Code.OSSS.GrandCoupling
import Code.OSSS.LindebergTree

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace OSSS

namespace GrandCouplingAssembly

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling StatMech.Probability

variable {E : Type*} [Fintype E] [DecidableEq E]









lemma codePrefix_congr_of_agree (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u u' : Fin n → ℝ) (m : ℕ) (hm : m ≤ n)
    (h : ∀ i : Fin n, (i : ℕ) < m → u i = u' i) :
    codePrefix μ σ u m = codePrefix μ σ u' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hmn : m < n := by omega
    have iheq : codePrefix μ σ u m = codePrefix μ σ u' m :=
      ih (by omega) (fun i hi => h i (by omega))
    conv_lhs => unfold codePrefix
    conv_rhs => unfold codePrefix
    simp only [hmn, dif_pos]
    rw [iheq, h ⟨m, hmn⟩ (Nat.lt_succ_self m)]



lemma codePrefix_step_congr (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u u' : Fin n → ℝ) (m : ℕ) (hmn : m < n)
    (hpre : codePrefix μ σ u m = codePrefix μ σ u' m)
    (hum : u ⟨m, hmn⟩ = u' ⟨m, hmn⟩) :
    codePrefix μ σ u (m+1) = codePrefix μ σ u' (m+1) := by
  conv_lhs => unfold codePrefix
  conv_rhs => unfold codePrefix
  simp only [hmn, dif_pos]
  rw [hpre, hum]



lemma codePrefix_forward (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u u' : Fin n → ℝ) (start : ℕ)
    (hagree : ∀ i : Fin n, start ≤ (i : ℕ) → u i = u' i)
    (hstart : codePrefix μ σ u start = codePrefix μ σ u' start) :
    ∀ m, start ≤ m → m ≤ n → codePrefix μ σ u m = codePrefix μ σ u' m := by
  intro m hsm hm
  obtain ⟨d, rfl⟩ : ∃ d, m = start + d := ⟨m - start, by omega⟩
  clear hsm
  induction d with
  | zero => simpa using hstart
  | succ d ih =>
    have hmn : start + d < n := by omega
    have hpre := ih (by omega)
    have hum : u ⟨start+d, hmn⟩ = u' ⟨start+d, hmn⟩ :=
      hagree ⟨start+d, hmn⟩ (Nat.le_add_right start d)
    have := codePrefix_step_congr μ σ u u' (start+d) hmn hpre hum
    convert this using 2



lemma codePrefix_det (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u u' : Fin n → ℝ) (k : ℕ) (hk : k < n)
    (hagree : ∀ i : Fin n, (i : ℕ) ≠ k → u i = u' i)
    (hbit : codePrefix μ σ u (k+1) (σ ⟨k, hk⟩) = codePrefix μ σ u' (k+1) (σ ⟨k, hk⟩)) :
    ∀ m, m ≤ n → codePrefix μ σ u m = codePrefix μ σ u' m := by
  have hk_agree : codePrefix μ σ u k = codePrefix μ σ u' k :=
    codePrefix_congr_of_agree μ σ u u' k (by omega) (fun i hi => hagree i (by omega))
  have hk1_agree : codePrefix μ σ u (k+1) = codePrefix μ σ u' (k+1) := by
    funext e
    by_cases he : e = σ ⟨k, hk⟩
    · subst he; exact hbit
    · conv_lhs => unfold codePrefix
      conv_rhs => unfold codePrefix
      simp only [hk, dif_pos]
      rw [Function.update_of_ne he, Function.update_of_ne he, hk_agree]
  intro m hm
  rcases le_or_gt m k with hmk | hmk
  · exact codePrefix_congr_of_agree μ σ u u' m hm (fun i hi => hagree i (by omega))
  · exact codePrefix_forward μ σ u u' (k+1) (fun i hi => hagree i (by omega)) hk1_agree m hmk hm





lemma codeMap_det (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (hσ : Function.Injective σ) (u u' : Fin n → ℝ) (k : ℕ) (hk : k < n)
    (hagree : ∀ i : Fin n, (i : ℕ) ≠ k → u i = u' i)
    (hbit : codeMap μ σ u (σ ⟨k, hk⟩) = codeMap μ σ u' (σ ⟨k, hk⟩)) :
    codeMap μ σ u = codeMap μ σ u' := by
  
  have hval : ∀ v : Fin n → ℝ,
      codeMap μ σ v (σ ⟨k, hk⟩) = codePrefix μ σ v (k+1) (σ ⟨k, hk⟩) := by
    intro v
    unfold codeMap
    exact codePrefix_stable μ σ hσ v (k+1) n hk (σ ⟨k, hk⟩)
      (by rw [mem_prefixSet_iff]; exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩)
  have hbit' : codePrefix μ σ u (k+1) (σ ⟨k, hk⟩) = codePrefix μ σ u' (k+1) (σ ⟨k, hk⟩) := by
    rw [← hval u, ← hval u', hbit]
  have := codePrefix_det μ σ u u' k hk hagree hbit' n le_rfl
  unfold codeMap
  exact this








lemma Wt_agree_off {n : ℕ} (U V : Fin n → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    ∀ i : Fin n, (i : ℕ) ≠ t - 1 → Wt U V t i = Wt U V (t-1) i := by
  intro i hi
  unfold Wt
  by_cases h : (i:ℕ) < t
  · have h' : (i:ℕ) < t - 1 := by omega
    simp [h, h']
  · have h' : ¬ (i:ℕ) < t - 1 := by omega
    simp [h, h']


lemma Wt_at_pos {n : ℕ} (U V : Fin n → ℝ) (t : ℕ) (ht : 1 ≤ t) (htn : t - 1 < n) :
    Wt U V t ⟨t-1, htn⟩ = V ⟨t-1, htn⟩ ∧ Wt U V (t-1) ⟨t-1, htn⟩ = U ⟨t-1, htn⟩ := by
  unfold Wt
  refine ⟨?_, ?_⟩
  · have h : (⟨t-1, htn⟩ : Fin n).val < t := by show t - 1 < t; omega
    simp [h]
  · have h : ¬ (⟨t-1, htn⟩ : Fin n).val < t - 1 := by show ¬ t - 1 < t - 1; exact lt_irrefl _
    simp only [h, if_false]










def sw (n s : ℕ) : Fin n ⊕ Fin n → Fin n ⊕ Fin n
  | Sum.inl i => if (i : ℕ) < s then Sum.inr i else Sum.inl i
  | Sum.inr i => if (i : ℕ) < s then Sum.inl i else Sum.inr i

lemma sw_invol (n s : ℕ) : Function.Involutive (sw n s) := by
  intro x
  cases x with
  | inl i => by_cases h : (i:ℕ) < s <;> simp [sw, h]
  | inr i => by_cases h : (i:ℕ) < s <;> simp [sw, h]


noncomputable def swEquiv (n s : ℕ) : Equiv.Perm (Fin n ⊕ Fin n) := (sw_invol n s).toPerm

lemma swEquiv_symm_apply (n s : ℕ) (x : Fin n ⊕ Fin n) :
    (swEquiv n s).symm x = sw n s x := rfl


def projInl (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) : Fin n → ℝ := fun i => w (Sum.inl i)



noncomputable def combine (n : ℕ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) ≃ᵐ (Fin n ⊕ Fin n → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)).symm

lemma combine_apply (n : ℕ) (U V : Fin n → ℝ) (x : Fin n ⊕ Fin n) :
    combine n (U, V) x = Sum.elim U V x := by cases x <;> rfl



noncomputable def selMap (n s : ℕ) : ((Fin n → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ) :=
  fun p => projInl n
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin n => ℝ) (swEquiv n s)) (combine n p))


lemma selMap_eq_Wt (n s : ℕ) (U V : Fin n → ℝ) : selMap n s (U, V) = Wt U V s := by
  funext i
  unfold selMap projInl Wt
  rw [MeasurableEquiv.coe_piCongrLeft]
  simp only [Equiv.piCongrLeft_apply, eq_rec_constant]
  rw [swEquiv_symm_apply, combine_apply]
  unfold sw
  by_cases h : (i:ℕ) < s <;> simp [h]



lemma selMap_measurePreserving (n s : ℕ) :
    MeasurePreserving (selMap n s) ((Vcube n).prod (Vcube n)) (Vcube n) := by
  show MeasurePreserving (selMap n s)
    ((Measure.pi (fun _ : Fin n => unitMeasure)).prod (Measure.pi (fun _ : Fin n => unitMeasure)))
    (Measure.pi (fun _ : Fin n => unitMeasure))
  have hcombine : MeasurePreserving (combine n)
      ((Measure.pi (fun _ : Fin n => unitMeasure)).prod (Measure.pi (fun _ : Fin n => unitMeasure)))
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure)) :=
    (measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin n => ℝ)
      (fun _ : Fin n ⊕ Fin n => unitMeasure)).symm _
  have hperm : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin n => ℝ) (swEquiv n s))
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure))
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure)) := by
    have h := measurePreserving_piCongrLeft (fun _ : Fin n ⊕ Fin n => unitMeasure) (swEquiv n s)
    convert h using 2
  have hproj : MeasurePreserving (projInl n)
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure))
      (Measure.pi (fun _ : Fin n => unitMeasure)) := by
    have hsum := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin n => ℝ)
      (fun _ : Fin n ⊕ Fin n => unitMeasure)
    have hfst : MeasurePreserving Prod.fst
        ((Measure.pi (fun _ : Fin n => unitMeasure)).prod (Measure.pi (fun _ : Fin n => unitMeasure)))
        (Measure.pi (fun _ : Fin n => unitMeasure)) := measurePreserving_fst
    have := hfst.comp hsum
    convert this using 1
  have := (hproj.comp hperm).comp hcombine
  convert this using 1










theorem integral_g_codeMap_Wt (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) (s : ℕ) :
    ∫ p, g (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s)) ∂((Vcube n).prod (Vcube n))
      = ∑ x, g x * μ x := by
  have hmp := selMap_measurePreserving n s
  have hae : AEStronglyMeasurable (fun w => g (codeMap μ (σ : Fin n → E) w)) (Vcube n) :=
    (measurable_g_codeMap μ σ g).aestronglyMeasurable
  have hcomp : ∫ p, (fun w => g (codeMap μ (σ : Fin n → E) w)) (selMap n s p)
        ∂((Vcube n).prod (Vcube n))
      = ∫ w, g (codeMap μ (σ : Fin n → E) w) ∂(Vcube n) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable, hmp.map_eq]
    rwa [hmp.map_eq]
  have hrw : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        (fun w => g (codeMap μ (σ : Fin n → E) w)) (selMap n s p))
      = (fun p => g (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s))) := by
    funext p; rw [show p = (p.1, p.2) from rfl, selMap_eq_Wt]
  rw [hrw] at hcomp
  rw [hcomp, integral_g_codeMap μ hpos hμ1 σ g]









lemma Wt_mono_prod {n : ℕ} (s : ℕ) :
    Monotone (fun p : (Fin n → ℝ) × (Fin n → ℝ) => Wt p.1 p.2 s) := by
  intro p p' hpp i
  unfold Wt
  rw [Prod.le_def] at hpp
  by_cases h : (i:ℕ) < s
  · simp only [h, if_true]; exact hpp.2 i
  · simp only [h, if_false]; exact hpp.1 i


lemma f_codeMap_Wt_mono_prod {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (s : ℕ) :
    Monotone (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (codeMap μ σ (Wt p.1 p.2 s))) :=
  fun _ _ hpp => hf ((codeMap_mono_u hpos hmono σ) ((Wt_mono_prod s) hpp))


lemma coord_codeMap_Wt_mono_prod {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E) (e : E) (s : ℕ) :
    Monotone (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Lindeberg.coord e (codeMap μ σ (Wt p.1 p.2 s))) :=
  fun _ _ hpp => Lindeberg.coord_mono e ((codeMap_mono_u hpos hmono σ) ((Wt_mono_prod s) hpp))


lemma measurable_g_codeMap_Wt_prod (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) (s : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        g (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s))) := by
  apply (measurable_g_codeMap μ σ g).comp
  apply measurable_pi_lambda
  intro i; unfold Wt
  by_cases h : (i:ℕ) < s
  · simp only [h, if_true]; exact (measurable_pi_apply i).comp measurable_snd
  · simp only [h, if_false]; exact (measurable_pi_apply i).comp measurable_fst








noncomputable def comb2 (n : ℕ) : ((Fin n → ℝ) × (Fin n → ℝ)) ≃ᵐ (Fin (n+n) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n+n) => ℝ) finSumFinEquiv)

lemma comb2_measurePreserving (n : ℕ) :
    MeasurePreserving (comb2 n) ((Vcube n).prod (Vcube n)) (Vcube (n+n)) := by
  show MeasurePreserving (comb2 n)
    ((Measure.pi (fun _ : Fin n => unitMeasure)).prod (Measure.pi (fun _ : Fin n => unitMeasure)))
    (Measure.pi (fun _ : Fin (n+n) => unitMeasure))
  unfold comb2
  have h1 : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)).symm
      ((Measure.pi (fun _ : Fin n => unitMeasure)).prod (Measure.pi (fun _ : Fin n => unitMeasure)))
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure)) :=
    (measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin n => ℝ)
      (fun _ : Fin n ⊕ Fin n => unitMeasure)).symm _
  have h2 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (n+n) => ℝ) (finSumFinEquiv (m := n) (n := n)))
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure))
      (Measure.pi (fun _ : Fin (n+n) => unitMeasure)) := by
    have h := measurePreserving_piCongrLeft (fun _ : Fin (n+n) => unitMeasure)
      (finSumFinEquiv (m := n) (n := n))
    convert h using 2
  exact h2.comp h1

lemma comb2_symm_fst (n : ℕ) (w : Fin (n+n) → ℝ) (i : Fin n) :
    ((comb2 n).symm w).1 i = w (finSumFinEquiv (Sum.inl i)) := by
  unfold comb2
  simp only [MeasurableEquiv.trans_symm, MeasurableEquiv.coe_trans, MeasurableEquiv.symm_symm,
    Function.comp_apply]
  rfl

lemma comb2_symm_snd (n : ℕ) (w : Fin (n+n) → ℝ) (i : Fin n) :
    ((comb2 n).symm w).2 i = w (finSumFinEquiv (Sum.inr i)) := by
  unfold comb2
  simp only [MeasurableEquiv.trans_symm, MeasurableEquiv.coe_trans, MeasurableEquiv.symm_symm,
    Function.comp_apply]
  rfl

lemma comb2_symm_mono (n : ℕ) : Monotone (comb2 n).symm := by
  intro w w' hww
  rw [Prod.le_def]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [comb2_symm_fst, comb2_symm_fst]; exact hww _
  · rw [comb2_symm_snd, comb2_symm_snd]; exact hww _



theorem hasFKG_prod_Vcube (n : ℕ) : HasFKG ((Vcube n).prod (Vcube n)) := by
  refine hasFKG_of_orderIso ((Vcube n).prod (Vcube n)) (Vcube (n+n)) (comb2 n)
    (comb2_measurePreserving n) (comb2_symm_mono n) ?_
  show HasFKG (Measure.pi (fun _ : Fin (n+n) => unitMeasure))
  exact hasFKG_pi_unitMeasure (n+n)


lemma abs_coord_le_one (e : E) (ω : ConfigSpace E) : |Lindeberg.coord e ω| ≤ 1 := by
  unfold Lindeberg.coord; split <;> norm_num







theorem grandCoupling_fkg_cross_prod {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (s₁ s₂ : ℕ) :
    (∫ p, f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₁)) ∂((Vcube n).prod (Vcube n)))
        * (∫ p, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₂))
            ∂((Vcube n).prod (Vcube n)))
      ≤ ∫ p, f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₁))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₂))
          ∂((Vcube n).prod (Vcube n)) :=
  hasFKG_prod_Vcube n _ _
    (measurable_g_codeMap_Wt_prod μ σ f s₁)
    (measurable_g_codeMap_Wt_prod μ σ (Lindeberg.coord e) s₂)
    ⟨Cf, fun _ => hfC _⟩ ⟨1, fun _ => abs_coord_le_one e _⟩
    (f_codeMap_Wt_mono_prod hpos hmono (σ : Fin n → E) hf s₁)
    (coord_codeMap_Wt_mono_prod hpos hmono (σ : Fin n → E) e s₂)








lemma coord_eq01 (e : E) (ω : ConfigSpace E) :
    Lindeberg.coord e ω = 0 ∨ Lindeberg.coord e ω = 1 := by
  unfold Lindeberg.coord; split
  · right; rfl
  · left; rfl




lemma tt_algebra (a b p q : ℝ) (hp : p = 0 ∨ p = 1) (hq : q = 0 ∨ q = 1)
    (hcmp : (b ≤ a ∧ q ≤ p) ∨ (a ≤ b ∧ p ≤ q)) (hdet : p = q → a = b) :
    |a - b| = b * q + a * p - b * p - a * q := by
  have key : |a - b| = (a - b) * (p - q) := by
    rcases hcmp with ⟨hab, hpq⟩ | ⟨hab, hpq⟩
    · rw [abs_of_nonneg (by linarith)]
      by_cases h : p = q
      · rw [hdet h, h]; ring
      · have hpq1 : p - q = 1 := by
          rcases hp with hp | hp <;> rcases hq with hq | hq <;> subst hp <;> subst hq <;>
            first | (exact absurd rfl h) | linarith
        rw [hpq1, mul_one]
    · rw [abs_of_nonpos (by linarith)]
      by_cases h : p = q
      · rw [hdet h, h]; ring
      · have hpq1 : p - q = -1 := by
          rcases hp with hp | hp <;> rcases hq with hq | hq <;> subst hp <;> subst hq <;>
            first | (exact absurd rfl h) | linarith
        rw [hpq1]; ring
  rw [key]; ring










theorem abs_step_eq_four_terms {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (t : ℕ) (ht : 1 ≤ t) (htn : t - 1 < n) (U V : Fin n → ℝ) :
    |f (codeMap μ (σ : Fin n → E) (Wt U V t))
        - f (codeMap μ (σ : Fin n → E) (Wt U V (t-1)))|
      = f (codeMap μ (σ : Fin n → E) (Wt U V (t-1)))
          * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V (t-1)))
        + f (codeMap μ (σ : Fin n → E) (Wt U V t))
          * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V t))
        - f (codeMap μ (σ : Fin n → E) (Wt U V (t-1)))
          * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V t))
        - f (codeMap μ (σ : Fin n → E) (Wt U V t))
          * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) := by
  set k := t - 1 with hk
  set e := (σ : Fin n → E) ⟨k, htn⟩ with he
  set Yt := codeMap μ (σ : Fin n → E) (Wt U V t) with hYt
  set Ys := codeMap μ (σ : Fin n → E) (Wt U V (t-1)) with hYs
  
  have hoff : ∀ i : Fin n, (i:ℕ) ≠ k → Wt U V t i = Wt U V (t-1) i := Wt_agree_off U V t ht
  
  have hdet : Lindeberg.coord e Yt = Lindeberg.coord e Ys → Yt = Ys := by
    intro hcoord
    have hbit : Yt e = Ys e := by
      unfold Lindeberg.coord at hcoord
      by_cases h1 : Yt e <;> by_cases h2 : Ys e <;> simp_all
    exact codeMap_det μ (σ : Fin n → E) σ.injective (Wt U V t) (Wt U V (t-1)) k htn
      (fun i hi => hoff i hi) hbit
  
  obtain ⟨hVt, hUt⟩ := Wt_at_pos U V t ht htn
  
  have hcmp : (f Ys ≤ f Yt ∧ Lindeberg.coord e Ys ≤ Lindeberg.coord e Yt)
      ∨ (f Yt ≤ f Ys ∧ Lindeberg.coord e Yt ≤ Lindeberg.coord e Ys) := by
    rcases le_total (U ⟨k, htn⟩) (V ⟨k, htn⟩) with hUV | hVU
    · left
      have hle : Wt U V (t-1) ≤ Wt U V t := by
        intro i
        by_cases hi : (i:ℕ) = k
        · have hieq : i = ⟨k, htn⟩ := by ext; rw [hi]
          rw [hieq, hVt, hUt]; exact hUV
        · rw [hoff i hi]
      have hY : Ys ≤ Yt := codeMap_mono_u hpos hmono (σ : Fin n → E) hle
      exact ⟨hf hY, Lindeberg.coord_mono e hY⟩
    · right
      have hle : Wt U V t ≤ Wt U V (t-1) := by
        intro i
        by_cases hi : (i:ℕ) = k
        · have hieq : i = ⟨k, htn⟩ := by ext; rw [hi]
          rw [hieq, hVt, hUt]; exact hVU
        · rw [hoff i hi]
      have hY : Yt ≤ Ys := codeMap_mono_u hpos hmono (σ : Fin n → E) hle
      exact ⟨hf hY, Lindeberg.coord_mono e hY⟩
  exact tt_algebra (f Yt) (f Ys) (Lindeberg.coord e Yt) (Lindeberg.coord e Ys)
    (coord_eq01 e Yt) (coord_eq01 e Ys) hcmp (fun h => by rw [hdet h])









lemma integrable_prod_obs (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (s₁ s₂ : ℕ) :
    Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₁))
          * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₂)))
      ((Vcube n).prod (Vcube n)) := by
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hfC (fun _ => false))
  refine ContinuousFKG.integrable_of_bdd _
    ((measurable_g_codeMap_Wt_prod μ σ f s₁).mul
      (measurable_g_codeMap_Wt_prod μ σ (Lindeberg.coord e) s₂)) (C := Cf * 1) (fun p => ?_)
  rw [abs_mul]
  exact mul_le_mul (hfC _) (abs_coord_le_one e _) (abs_nonneg _) hCf0


lemma sum_eq_mean (μ : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) :
    ∑ x, g x * μ x = Lindeberg.mean μ g := rfl










theorem step_le_two_cov {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf)
    (t : ℕ) (ht : 1 ≤ t) (htn : t - 1 < n) :
    (∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 t))
            - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (t-1)))| ∂((Vcube n).prod (Vcube n)))
      ≤ 2 * Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)) := by
  set e := (σ : Fin n → E) ⟨t-1, htn⟩ with he
  
  set D1 := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
    f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (t-1)))
      * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (t-1))) with hD1
  set D2 := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
    f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 t))
      * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 t)) with hD2
  set C1 := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
    f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (t-1)))
      * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 t)) with hC1
  set C2 := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
    f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 t))
      * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (t-1))) with hC2
  have hI1 : Integrable D1 ((Vcube n).prod (Vcube n)) := integrable_prod_obs μ σ hfC e (t-1) (t-1)
  have hI2 : Integrable D2 ((Vcube n).prod (Vcube n)) := integrable_prod_obs μ σ hfC e t t
  have hIc1 : Integrable C1 ((Vcube n).prod (Vcube n)) := integrable_prod_obs μ σ hfC e (t-1) t
  have hIc2 : Integrable C2 ((Vcube n).prod (Vcube n)) := integrable_prod_obs μ σ hfC e t (t-1)
  
  have hcongr : (∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 t))
            - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (t-1)))| ∂((Vcube n).prod (Vcube n)))
      = ∫ p, (D1 p + D2 p - C1 p - C2 p) ∂((Vcube n).prod (Vcube n)) := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro p
    exact abs_step_eq_four_terms hpos hmono σ hf t ht htn p.1 p.2
  rw [hcongr]
  
  have esplit : (fun p => D1 p + D2 p - C1 p - C2 p) = (D1 + D2 - C1) - C2 := by
    funext p; simp only [Pi.add_apply, Pi.sub_apply]
  rw [show (∫ p, (D1 p + D2 p - C1 p - C2 p) ∂((Vcube n).prod (Vcube n)))
        = ∫ p, ((D1 + D2 - C1) - C2) p ∂((Vcube n).prod (Vcube n)) from by rw [esplit]]
  rw [integral_sub' ((hI1.add hI2).sub hIc1) hIc2]
  rw [show (∫ p, (D1 + D2 - C1) p ∂((Vcube n).prod (Vcube n)))
        = ∫ p, ((D1 + D2) - C1) p ∂((Vcube n).prod (Vcube n)) from rfl]
  rw [integral_sub' (hI1.add hI2) hIc1, integral_add' hI1 hI2]
  
  have hbbb1 : (∫ p, D1 p ∂((Vcube n).prod (Vcube n)))
      = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) := by
    rw [hD1, integral_g_codeMap_Wt μ hpos hμ1 σ (fun ω => f ω * Lindeberg.coord e ω) (t-1)]
    rfl
  have hbbb2 : (∫ p, D2 p ∂((Vcube n).prod (Vcube n)))
      = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) := by
    rw [hD2, integral_g_codeMap_Wt μ hpos hμ1 σ (fun ω => f ω * Lindeberg.coord e ω) t]
    rfl
  
  have hmeanf_s : (∫ p, f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (t-1))) ∂((Vcube n).prod (Vcube n)))
      = Lindeberg.mean μ f := by
    rw [integral_g_codeMap_Wt μ hpos hμ1 σ f (t-1)]; rfl
  have hmeanf_t : (∫ p, f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 t)) ∂((Vcube n).prod (Vcube n)))
      = Lindeberg.mean μ f := by
    rw [integral_g_codeMap_Wt μ hpos hμ1 σ f t]; rfl
  have hmeanc_s : (∫ p, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (t-1)))
        ∂((Vcube n).prod (Vcube n)))
      = Lindeberg.mean μ (Lindeberg.coord e) := by
    rw [integral_g_codeMap_Wt μ hpos hμ1 σ (Lindeberg.coord e) (t-1)]; rfl
  have hmeanc_t : (∫ p, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 t))
        ∂((Vcube n).prod (Vcube n)))
      = Lindeberg.mean μ (Lindeberg.coord e) := by
    rw [integral_g_codeMap_Wt μ hpos hμ1 σ (Lindeberg.coord e) t]; rfl
  
  have hFKG1 : Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
      ≤ ∫ p, C1 p ∂((Vcube n).prod (Vcube n)) := by
    have := grandCoupling_fkg_cross_prod hpos hmono σ hf hfC e (t-1) t
    rw [hmeanf_s, hmeanc_t] at this
    exact this
  have hFKG2 : Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
      ≤ ∫ p, C2 p ∂((Vcube n).prod (Vcube n)) := by
    have := grandCoupling_fkg_cross_prod hpos hmono σ hf hfC e t (t-1)
    rw [hmeanf_t, hmeanc_s] at this
    exact this
  
  rw [hbbb1, hbbb2]
  have hcov : Lindeberg.cov μ f (Lindeberg.coord e)
      = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω)
        - Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e) := rfl
  rw [hcov]
  linarith [hFKG1, hFKG2]








lemma Wt_zero {n : ℕ} (U V : Fin n → ℝ) : Wt U V 0 = U := by
  funext i; unfold Wt; simp


lemma Wt_card {n : ℕ} (U V : Fin n → ℝ) : Wt U V n = V := by
  funext i; unfold Wt; simp [i.2]



lemma integral_two_codeMap (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (h : ConfigSpace E → ConfigSpace E → ℝ)
    {Ch : ℝ} (hC : ∀ x y, |h x y| ≤ Ch) :
    ∫ p, h (codeMap μ (σ : Fin n → E) p.1) (codeMap μ (σ : Fin n → E) p.2)
        ∂((Vcube n).prod (Vcube n))
      = ∑ x, (∑ y, h x y * μ y) * μ x := by
  have hmeas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      h (codeMap μ (σ : Fin n → E) p.1) (codeMap μ (σ : Fin n → E) p.2)) :=
    (measurable_of_finite (fun q : ConfigSpace E × ConfigSpace E => h q.1 q.2)).comp
      (((measurable_codeMap μ σ).comp measurable_fst).prodMk
        ((measurable_codeMap μ σ).comp measurable_snd))
  have hint : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      h (codeMap μ (σ : Fin n → E) p.1) (codeMap μ (σ : Fin n → E) p.2))
      ((Vcube n).prod (Vcube n)) :=
    ContinuousFKG.integrable_of_bdd _ hmeas (fun p => hC _ _)
  rw [integral_prod _ hint]
  rw [show (fun U => ∫ V, h (codeMap μ (σ:Fin n→E) U) (codeMap μ (σ:Fin n→E) V) ∂(Vcube n))
        = (fun U => ∑ y, h (codeMap μ (σ:Fin n→E) U) y * μ y) from by
    funext U
    exact integral_g_codeMap μ hpos hμ1 σ (fun y => h (codeMap μ (σ:Fin n→E) U) y)]
  rw [integral_g_codeMap μ hpos hμ1 σ (fun x => ∑ y, h x y * μ y)]


lemma abs_f_diff_le_one {f : ConfigSpace E → ℝ} (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (x y : ConfigSpace E) : |f x - f y| ≤ 1 := by
  have hx0 : 0 ≤ f x := hf0 x
  have hy0 : 0 ≤ f y := hf0 y
  rw [abs_le]
  exact ⟨by linarith [hf1 y], by linarith [hf1 x]⟩







theorem var_le_grandCoupling_first_step {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var μ f
      ≤ (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 0))
            - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 n))| ∂((Vcube n).prod (Vcube n)) := by
  
  have hrw : (∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 0))
            - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 n))| ∂((Vcube n).prod (Vcube n)))
      = ∑ x, (∑ y, |f x - f y| * μ y) * μ x := by
    have hsimp : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 0))
            - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 n))|)
        = (fun p => (fun x y => |f x - f y|) (codeMap μ (σ : Fin n → E) p.1)
              (codeMap μ (σ : Fin n → E) p.2)) := by
      funext p; rw [Wt_zero, Wt_card]
    rw [hsimp, integral_two_codeMap μ hpos hμ1 σ (fun x y => |f x - f y|)
      (Ch := 1) (fun x y => by rw [abs_abs]; exact abs_f_diff_le_one hf0 hf1 x y)]
  rw [hrw, Lindeberg.var_eq_double_sum μ hμ1 f]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
  apply Finset.sum_le_sum
  intro x _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro y _
  
  have hbound : |f x - f y| ≤ 1 := abs_f_diff_le_one hf0 hf1 x y
  have hsq : (f x - f y) ^ 2 ≤ |f x - f y| := by
    calc (f x - f y) ^ 2 = |f x - f y| * |f x - f y| := by
          rw [abs_mul_abs_self, sq]
      _ ≤ |f x - f y| * 1 := mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
      _ = |f x - f y| := by ring
  have hμx : 0 ≤ μ x := (hpos x).le
  have hμy : 0 ≤ μ y := (hpos y).le
  nlinarith [hsq, hμx, hμy, mul_nonneg hμx hμy, abs_nonneg (f x - f y)]




theorem grandCoupling_telescope {μ : ConfigSpace E → ℝ} {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) :
    (∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 0))
            - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 n))| ∂((Vcube n).prod (Vcube n)))
      ≤ ∑ t ∈ Finset.range n,
          ∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (t+1)))
                - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 t))| ∂((Vcube n).prod (Vcube n)) := by
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hfC (fun _ => false))
  
  have hintdiff : ∀ s₁ s₂ : ℕ, Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₁))
        - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₂))|) ((Vcube n).prod (Vcube n)) := by
    intro s₁ s₂
    refine ContinuousFKG.integrable_of_bdd _
      (((measurable_g_codeMap_Wt_prod μ σ f s₁).sub
        (measurable_g_codeMap_Wt_prod μ σ f s₂)).abs) (C := 2*Cf) (fun p => ?_)
    rw [abs_abs]
    calc |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₁))
            - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₂))|
        ≤ |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₁))|
          + |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₂))| := abs_sub _ _
      _ ≤ 2*Cf := by linarith [hfC (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₁)),
                                hfC (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₂))]
  
  rw [← integral_finsetSum (Finset.range n) (fun t _ => hintdiff (t+1) t)]
  
  apply integral_mono (hintdiff 0 n)
  · apply integrable_finsetSum; intro t _; exact hintdiff (t+1) t
  · intro p
    set F : ℕ → ℝ := fun s => f (codeMap μ (σ:Fin n→E) (Wt p.1 p.2 s)) with hF
    show |F 0 - F n| ≤ ∑ t ∈ Finset.range n, |F (t+1) - F t|
    have htel : F 0 - F n = ∑ t ∈ Finset.range n, (F t - F (t+1)) := by
      rw [Finset.sum_range_sub' F n]
    rw [htel]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    apply Finset.sum_congr rfl; intro t _; rw [abs_sub_comm]
















theorem tree_osss_unconditional {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var μ f ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
  classical
  set n := Fintype.card E with hn
  set σ : Fin n ≃ E := (Fintype.equivFin E).symm with hσ
  have hf0' : ∀ ω, (0:ℝ) ≤ f ω := fun ω => hf0 ω
  have hfC : ∀ ω, |f ω| ≤ 1 := fun ω => by
    rw [abs_le]; exact ⟨by linarith [hf0' ω], hf1 ω⟩
  
  refine (var_le_grandCoupling_first_step hpos hμ1 σ hf0 hf1).trans ?_
  refine (mul_le_mul_of_nonneg_left (grandCoupling_telescope σ hfC) (by norm_num : (0:ℝ) ≤ 1/2)).trans ?_
  
  rw [Finset.mul_sum]
  
  have hstep : ∀ i : Fin n,
      (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 ((i:ℕ)+1)))
              - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (i:ℕ)))| ∂((Vcube n).prod (Vcube n))
        ≤ Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) i)) := by
    intro i
    have hpos1 : (1:ℕ) ≤ (i:ℕ) + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hbound2 : (∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 ((i:ℕ)+1)))
            - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (i:ℕ)))| ∂((Vcube n).prod (Vcube n)))
        ≤ 2 * Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) i)) := by
      
      
      have htn : ((i:ℕ)+1) - 1 < n := by
        have h : ((i:ℕ)+1) - 1 = (i:ℕ) := by omega
        rw [h]; exact i.2
      have hbound := step_le_two_cov hpos hμ1 hmono σ hf hfC ((i:ℕ)+1) hpos1 htn
      have heq : ((i:ℕ)+1) - 1 = (i:ℕ) := by omega
      have hi : (⟨((i:ℕ)+1) - 1, htn⟩ : Fin n) = i := by
        apply Fin.ext; show ((i:ℕ)+1) - 1 = (i:ℕ); omega
      simp only [hi] at hbound
      rwa [heq] at hbound
    linarith [hbound2]
  calc ∑ t ∈ Finset.range n,
        (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (t+1)))
                - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 t))| ∂((Vcube n).prod (Vcube n))
      = ∑ i : Fin n,
          (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 ((i:ℕ)+1)))
                - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (i:ℕ)))| ∂((Vcube n).prod (Vcube n)) := by
        rw [Finset.sum_range (fun t =>
          (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 (t+1)))
                  - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 t))| ∂((Vcube n).prod (Vcube n)))]
    _ ≤ ∑ i : Fin n, Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) i)) :=
        Finset.sum_le_sum (fun i _ => hstep i)
    _ = ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) :=
        Equiv.sum_comp σ (fun e => Lindeberg.cov μ f (Lindeberg.coord e))








open OSSS.MonotonicMeasure in






theorem osss_monotonicOSSSBound {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    MonotonicOSSSBound μ Finset.univ f 1 1 1 := by
  unfold MonotonicOSSSBound
  rw [← Lindeberg.var_eq_genVar, Nat.cast_one, one_mul, one_mul, one_mul]
  refine (tree_osss_unconditional hpos hμ1 hmono hf hf0 hf1).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro e _
  rw [← Lindeberg.cov_eq_genCov, ← Lindeberg.coord_eq_genCoord]
  unfold Lindeberg.cov Lindeberg.mean
  rw [show (fun ω => f ω * Lindeberg.coord e ω) = (fun ω => Lindeberg.coord e ω * f ω) from by
    funext ω; ring]
  ring






section FK

open StatMech.OSSS.MonotonicFK









theorem fk_q2_osss {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ConfigSpace (Sym2 V) → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var (fkMass G p 2) f
      ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) :=
  tree_osss_unconditional
    (fun ω => fkMass_pos G hp hp1 (by norm_num) ω)
    (fkMass_sum_eq_one G hp hp1 (by norm_num))
    (fkMass_isMonotonic G hp hp1 (by norm_num)) hf hf0 hf1

open OSSS.MonotonicMeasure in




theorem fk_q2_monotonicOSSSBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {f : ConfigSpace (Sym2 V) → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    MonotonicOSSSBound (fkMass G p 2) Finset.univ f 1 1 1 :=
  osss_monotonicOSSSBound
    (fun ω => fkMass_pos G hp hp1 (by norm_num) ω)
    (fkMass_sum_eq_one G hp hp1 (by norm_num))
    (fkMass_isMonotonic G hp hp1 (by norm_num)) hf hf0 hf1

end FK

end GrandCouplingAssembly

end OSSS

end StatMech
