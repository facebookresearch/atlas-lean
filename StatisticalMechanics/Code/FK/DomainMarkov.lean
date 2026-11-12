/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































import Mathlib
import Code.Foundations.ConfigSpace
import Code.FK.RandomCluster

open scoped BigOperators

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]





def AgreesOff (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ConfigSpace (Sym2 V) → Prop :=
  fun ω => ∀ e, e ∉ F → ω e = ψ e

instance (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    DecidablePred (AgreesOff F ψ) := by
  intro ω; unfold AgreesOff; infer_instance

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem agreesOff_self (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    AgreesOff F ψ ψ := fun _ _ => rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem agreesOff_symm {F : Finset (Sym2 V)} {ψ ω : ConfigSpace (Sym2 V)}
    (h : AgreesOff F ψ ω) : AgreesOff F ω ψ := fun e he => (h e he).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem agreesOff_congr {F : Finset (Sym2 V)} {ψ ω : ConfigSpace (Sym2 V)}
    (h : AgreesOff F ψ ω) : AgreesOff F ψ = AgreesOff F ω := by
  funext ρ
  simp only [eq_iff_iff]
  constructor
  · intro hρ e he; rw [hρ e he, h e he]
  · intro hρ e he; rw [hρ e he, ← h e he]


noncomputable def condFibre (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    Finset (ConfigSpace (Sym2 V)) :=
  Finset.univ.filter (AgreesOff F ψ)

omit [DecidableRel G.Adj] in
@[simp] theorem mem_condFibre {F : Finset (Sym2 V)} {ψ ω : ConfigSpace (Sym2 V)} :
    ω ∈ condFibre F ψ ↔ AgreesOff F ψ ω := by
  unfold condFibre; simp

omit [DecidableRel G.Adj] in
theorem self_mem_condFibre (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ψ ∈ condFibre F ψ := by rw [mem_condFibre]; exact agreesOff_self F ψ













noncomputable def inducedFkZ (p q : ℝ) (F : Finset (Sym2 V))
    (ψ : ConfigSpace (Sym2 V)) : ℝ :=
  ∑ ρ ∈ condFibre F ψ, fkWeight G p q ρ



theorem inducedFkZ_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    0 < inducedFkZ G p q F ψ := by
  unfold inducedFkZ
  exact Finset.sum_pos (fun ρ _ => fkWeight_pos G hp hp1 hq ρ)
    ⟨ψ, self_mem_condFibre F ψ⟩

theorem inducedFkZ_ne_zero {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    inducedFkZ G p q F ψ ≠ 0 :=
  (inducedFkZ_pos G hp hp1 hq F ψ).ne'




noncomputable def inducedFkProb (p q : ℝ) (F : Finset (Sym2 V))
    (ψ ω : ConfigSpace (Sym2 V)) : ℝ :=
  fkWeight G p q ω / inducedFkZ G p q F ψ


theorem inducedFkProb_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ ω : ConfigSpace (Sym2 V)) :
    0 ≤ inducedFkProb G p q F ψ ω :=
  div_nonneg (fkWeight_nonneg G hp hp1 hq ω) (inducedFkZ_pos G hp hp1 hq F ψ).le


theorem inducedFkProb_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ ω : ConfigSpace (Sym2 V)) :
    0 < inducedFkProb G p q F ψ ω :=
  div_pos (fkWeight_pos G hp hp1 hq ω) (inducedFkZ_pos G hp hp1 hq F ψ)



theorem inducedFkProb_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ∑ ω ∈ condFibre F ψ, inducedFkProb G p q F ψ ω = 1 := by
  unfold inducedFkProb
  rw [← Finset.sum_div]
  exact div_self (inducedFkZ_ne_zero G hp hp1 hq F ψ)






noncomputable def condFkProb (p q : ℝ) (F : Finset (Sym2 V))
    (ψ ω : ConfigSpace (Sym2 V)) : ℝ :=
  fkProb G p q ω / ∑ ρ ∈ condFibre F ψ, fkProb G p q ρ




theorem condFibre_fkProb_sum {p q : ℝ} (F : Finset (Sym2 V))
    (ψ : ConfigSpace (Sym2 V)) :
    ∑ ρ ∈ condFibre F ψ, fkProb G p q ρ = inducedFkZ G p q F ψ / fkZ G p q := by
  unfold fkProb inducedFkZ
  rw [Finset.sum_div]












theorem condFkProb_eq_inducedFkProb {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ ω : ConfigSpace (Sym2 V)) :
    condFkProb G p q F ψ ω = inducedFkProb G p q F ψ ω := by
  unfold condFkProb inducedFkProb
  rw [condFibre_fkProb_sum]
  unfold fkProb
  rw [div_div_div_cancel_right₀]
  · exact fkZ_ne_zero G hp hp1 hq




theorem condFkProb_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ∑ ω ∈ condFibre F ψ, condFkProb G p q F ψ ω = 1 := by
  rw [Finset.sum_congr rfl
    (fun ω _ => condFkProb_eq_inducedFkProb G hp hp1 hq F ψ ω)]
  exact inducedFkProb_sum_eq_one G hp hp1 hq F ψ




theorem inducedFkZ_congr {p q : ℝ} {F : Finset (Sym2 V)} {ψ ψ' : ConfigSpace (Sym2 V)}
    (h : AgreesOff F ψ ψ') : inducedFkZ G p q F ψ = inducedFkZ G p q F ψ' := by
  unfold inducedFkZ
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ρ
  simp only [mem_condFibre]
  rw [agreesOff_congr h]

end FK

end StatMech
