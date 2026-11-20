/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Mathlib
import Code.Inequalities.FKG
import Code.Sharpness.FieldGhostDict
import Code.Walls.ghysupermult

open Finset Classical

set_option maxHeartbeats 1600000

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]




lemma ghsvp_wJ_zero_factor (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (s : ConfigSpace W) :
    wJ E J (fun _ => 0) s =
      ∏ e ∈ E, (Real.cosh (J e) + bond s e * Real.sinh (J e)) := by
  unfold wJ
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro e _
  exact exp_mul_pm (J e) (bond s e) (bond_eq_pm s e)


lemma ghsvp_wJ_factor (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hf : W -> Real) (s : ConfigSpace W) :
    wJ E J hf s =
      (∏ e ∈ E, (Real.cosh (J e) + bond s e * Real.sinh (J e))) *
        ∏ x : W, (Real.cosh (hf x) + spin s x * Real.sinh (hf x)) := by
  unfold wJ
  rw [Real.exp_add, Real.exp_sum, Real.exp_sum]
  congr 1
  · apply Finset.prod_congr rfl
    intro e _
    exact exp_mul_pm (J e) (bond s e) (bond_eq_pm s e)
  · apply Finset.prod_congr rfl
    intro x _
    exact exp_mul_pm (hf x) (spin s x) (spin_eq_pm s x)


lemma ghsvp_expJ_nonneg (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hf : W -> Real) (hJ : ∀ e ∈ E, 0 <= J e) (hhf : ∀ x, 0 <= hf x)
    (A : Finset W) : 0 <= expJ E J hf (spinProd A) := by
  unfold expJ
  apply div_nonneg
  · rw [show (∑ s : ConfigSpace W, spinProd A s * wJ E J hf s) =
        ∑ s : ConfigSpace W, spinProd A s *
          ((∏ e ∈ E, (Real.cosh (J e) + bond s e * Real.sinh (J e))) *
            ∏ x : W, (Real.cosh (hf x) + spin s x * Real.sinh (hf x))) by
      apply Finset.sum_congr rfl
      intro s _
      rw [ghsvp_wJ_factor]]
    exact inner_sum_nonneg' E
      (fun e => Real.cosh (J e)) (fun e => Real.sinh (J e))
      (fun x => Real.cosh (hf x)) (fun x => Real.sinh (hf x))
      (fun e _ => (Real.cosh_pos _).le)
      (fun e he => Real.sinh_nonneg_iff.mpr (hJ e he))
      (fun x => (Real.cosh_pos _).le)
      (fun x => Real.sinh_nonneg_iff.mpr (hhf x))
      (spinProd A) (isSpinMonomial_spinProd A)
  · exact (ZJ_pos E J hf).le


lemma ghsvp_expJ_zero_nonneg (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e) (A : Finset W) :
    0 <= expJ E J (fun _ => 0) (spinProd A) := by
  unfold expJ
  apply div_nonneg
  · rw [show (∑ s : ConfigSpace W, spinProd A s * wJ E J (fun _ => 0) s) =
        ∑ s : ConfigSpace W, spinProd A s *
          ∏ e ∈ E, (Real.cosh (J e) + Real.sinh (J e) * bond s e) by
      apply Finset.sum_congr rfl
      intro s _
      rw [ghsvp_wJ_zero_factor]
      congr 1
      apply Finset.prod_congr rfl
      intro e _
      ring]
    simpa [mul_comm] using inner_sum_nonneg' E
      (fun e => Real.cosh (J e)) (fun e => Real.sinh (J e))
      (fun _ => 1) (fun _ => 0)
      (fun e _ => (Real.cosh_pos _).le)
      (fun e he => Real.sinh_nonneg_iff.mpr (hJ e he))
      (fun _ => by norm_num) (fun _ => by norm_num)
      (spinProd A) (isSpinMonomial_spinProd A)
  · exact (ZJ_pos E J (fun _ => 0)).le


lemma ghsvp_ZJ_zero_mono (J : Sym2 W -> Real) (hJ : forall e, 0 <= J e)
    (E F : Finset (Sym2 W)) (hEF : E ⊆ F) (hnd : ∀ e ∈ F, ¬ e.IsDiag) :
    ZJ E J (fun _ => 0) <= ZJ F J (fun _ => 0) := by
  have hadd : ∀ D : Finset (Sym2 W), Disjoint D E → (∀ e ∈ D, ¬ e.IsDiag) →
      ZJ E J (fun _ => 0) <= ZJ (D ∪ E) J (fun _ => 0) := by
    intro D
    induction D using Finset.induction with
    | empty => simp
    | @insert e D he ih =>
        intro hdisj hdiag
        have hdisjD : Disjoint D E := hdisj.mono_left (Finset.subset_insert e D)
        have hdiagD : ∀ a ∈ D, ¬ a.IsDiag :=
          fun a ha => hdiag a (Finset.mem_insert_of_mem ha)
        have hi := ih hdisjD hdiagD
        have heE : e ∉ E := fun heE =>
          (Finset.disjoint_left.mp hdisj (Finset.mem_insert_self e D)) heE
        obtain ⟨x, y, hxy, rfl⟩ :=
          exists_pair_of_not_isDiag (hdiag e (Finset.mem_insert_self e D))
        have hedge : s(x, y) ∉ D ∪ E := by simp [he, heE]
        have hins := ghy_ZJ_insert_factor (D ∪ E) J (fun _ => 0) hxy hedge
        have hcorr : 0 <= expJ (D ∪ E) J (fun _ => 0) (spinProd {x, y}) :=
          ghsvp_expJ_zero_nonneg (D ∪ E) J (fun a _ => hJ a) {x, y}
        have hc : 1 <= Real.cosh (J s(x, y)) := Real.one_le_cosh _
        have hs : 0 <= Real.sinh (J s(x, y)) := Real.sinh_nonneg_iff.mpr (hJ _)
        have hstep : ZJ (D ∪ E) J (fun _ => 0) <=
            ZJ (insert s(x, y) (D ∪ E)) J (fun _ => 0) := by
          rw [hins]
          nlinarith [ZJ_pos (D ∪ E) J (fun _ => 0), mul_nonneg hs hcorr]
        rw [Finset.insert_union]
        exact hi.trans hstep
  have h := hadd (F \ E) Finset.sdiff_disjoint (by
    intro e he
    exact hnd e (Finset.mem_sdiff.mp he).1)
  rwa [Finset.sdiff_union_of_subset hEF] at h


lemma ghsvp_ZJ_zero_logSupermodular (J : Sym2 W -> Real) (hJ : forall e, 0 <= J e)
    (E F : Finset (Sym2 W)) (hnd : ∀ e ∈ E ∪ F, ¬ e.IsDiag) :
    ZJ E J (fun _ => 0) * ZJ F J (fun _ => 0) <=
      ZJ (E ∪ F) J (fun _ => 0) * ZJ (E ∩ F) J (fun _ => 0) := by
  have hsub : E ∩ F ⊆ E := Finset.inter_subset_left
  have hdisj : Disjoint (F \ E) E := Finset.sdiff_disjoint
  have hndE : ∀ e ∈ E, ¬ e.IsDiag := fun e he => hnd e (Finset.mem_union_left F he)
  have hndD : ∀ e ∈ F \ E, ¬ e.IsDiag := by
    intro e he
    exact hnd e (Finset.mem_union_right E (Finset.mem_sdiff.mp he).1)
  have h := ghy_ZJ_supermod J (fun _ => 0) hJ (fun _ => le_rfl)
    (E ∩ F) E hsub hndE (F \ E) hdisj hndD
  have hleft : (E ∩ F) ∪ (F \ E) = F := by
    ext e
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hright : E ∪ (F \ E) = E ∪ F := by
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [hleft, hright] at h
  nlinarith [h]




def ghsvp_vertexEdges (E : Finset (Sym2 W)) (S : Finset W) : Finset (Sym2 W) :=
  E.filter (Sharpness.edgeInside S)


noncomputable def ghsvp_vertexZ (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (S : Finset W) : Real :=
  ZJ (ghsvp_vertexEdges E S) J (fun _ => 0)

lemma ghsvp_vertexEdges_mono (E : Finset (Sym2 W)) :
    Monotone (ghsvp_vertexEdges E) := by
  intro S T hST e he
  rw [ghsvp_vertexEdges, Finset.mem_filter] at he ⊢
  exact ⟨he.1, fun x hx => hST (he.2 x hx)⟩

lemma ghsvp_vertexEdges_inter (E : Finset (Sym2 W)) (S T : Finset W) :
    ghsvp_vertexEdges E (S ∩ T) = ghsvp_vertexEdges E S ∩ ghsvp_vertexEdges E T := by
  ext e
  induction e with
  | h a b => simp [ghsvp_vertexEdges, Sharpness.edgeInside, and_assoc, and_left_comm, and_comm]

lemma ghsvp_vertexEdges_union_subset (E : Finset (Sym2 W)) (S T : Finset W) :
    ghsvp_vertexEdges E S ∪ ghsvp_vertexEdges E T ⊆ ghsvp_vertexEdges E (S ∪ T) :=
  Finset.union_subset ((ghsvp_vertexEdges_mono E) Finset.subset_union_left)
    ((ghsvp_vertexEdges_mono E) Finset.subset_union_right)


theorem ghsvp_vertexZ_logSupermodular (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hJ : forall e, 0 <= J e) (hnd : ∀ e ∈ E, ¬ e.IsDiag) (S T : Finset W) :
    ghsvp_vertexZ E J S * ghsvp_vertexZ E J T <=
      ghsvp_vertexZ E J (S ∪ T) * ghsvp_vertexZ E J (S ∩ T) := by
  unfold ghsvp_vertexZ
  let ES := ghsvp_vertexEdges E S
  let ET := ghsvp_vertexEdges E T
  have hlat := ghsvp_ZJ_zero_logSupermodular J hJ ES ET (by
    intro e he
    rw [Finset.mem_union] at he
    exact he.elim (fun h => hnd e (Finset.mem_filter.mp h).1)
      (fun h => hnd e (Finset.mem_filter.mp h).1))
  have hmono := ghsvp_ZJ_zero_mono J hJ (ES ∪ ET)
    (ghsvp_vertexEdges E (S ∪ T)) (ghsvp_vertexEdges_union_subset E S T) (by
      intro e he
      exact hnd e (Finset.mem_filter.mp he).1)
  dsimp [ES, ET] at hlat hmono
  rw [← ghsvp_vertexEdges_inter] at hlat
  have hz : 0 <= ZJ (ghsvp_vertexEdges E (S ∩ T)) J (fun _ => 0) :=
    (ZJ_pos _ _ _).le
  exact hlat.trans (mul_le_mul_of_nonneg_right hmono hz)


noncomputable def ghsvp_vertexCorr (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (S P : Finset W) : Real :=
  expJ (ghsvp_vertexEdges E S) J (fun _ => 0) (spinProd P)


noncomputable def ghsvp_vertexCorrField (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hf : W -> Real) (S P : Finset W) : Real :=
  expJ (ghsvp_vertexEdges E S) J hf (spinProd P)

theorem ghsvp_vertexCorr_nonneg (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hJ : ∀ e, 0 <= J e) (S P : Finset W) :
    0 <= ghsvp_vertexCorr E J S P := by
  exact ghsvp_expJ_zero_nonneg _ J (fun e _ => hJ e) P


theorem ghsvp_vertexCorr_mono (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hJ : ∀ e, 0 <= J e) (hnd : ∀ e ∈ E, ¬ e.IsDiag)
    {S T : Finset W} (hST : S ⊆ T) (P : Finset W) :
    ghsvp_vertexCorr E J S P <= ghsvp_vertexCorr E J T P := by
  unfold ghsvp_vertexCorr
  apply griffiths_mono (ghsvp_vertexEdges E S) (ghsvp_vertexEdges E T) J
    (fun _ => 0) ((ghsvp_vertexEdges_mono E) hST)
  · exact fun e _ => hJ e
  · exact fun _ => le_rfl
  · intro e he _
    exact hnd e (Finset.mem_filter.mp he).1

theorem ghsvp_vertexCorrField_nonneg (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hf : W -> Real) (hJ : ∀ e, 0 <= J e) (hhf : ∀ x, 0 <= hf x)
    (S P : Finset W) : 0 <= ghsvp_vertexCorrField E J hf S P := by
  exact ghsvp_expJ_nonneg _ J hf (fun e _ => hJ e) hhf P

theorem ghsvp_vertexCorrField_mono (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hf : W -> Real) (hJ : ∀ e, 0 <= J e) (hhf : ∀ x, 0 <= hf x)
    (hnd : ∀ e ∈ E, ¬ e.IsDiag) {S T : Finset W} (hST : S ⊆ T) (P : Finset W) :
    ghsvp_vertexCorrField E J hf S P <= ghsvp_vertexCorrField E J hf T P := by
  unfold ghsvp_vertexCorrField
  apply griffiths_mono (ghsvp_vertexEdges E S) (ghsvp_vertexEdges E T) J hf
    ((ghsvp_vertexEdges_mono E) hST)
  · exact fun e _ => hJ e
  · exact hhf
  · intro e he _
    exact hnd e (Finset.mem_filter.mp he).1




def ghsvp_mergeConfig (S : Finset W) (a : (↑S -> Bool))
    (b : ({v : W // v ∉ S}) -> Bool) : ConfigSpace W :=
  fun v => if hv : v ∈ S then a ⟨v, hv⟩ else b ⟨v, hv⟩


def ghsvp_splitConfig (S : Finset W) :
    ConfigSpace W ≃ ((↑S -> Bool) × (({v : W // v ∉ S}) -> Bool)) where
  toFun s := (λ v => s v, λ v => s v)
  invFun p := ghsvp_mergeConfig S p.1 p.2
  left_inv s := by
    funext v
    simp only [ghsvp_mergeConfig]
    split <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext v
      simp [ghsvp_mergeConfig, v.property]
    · funext v
      simp [ghsvp_mergeConfig, v.property]


theorem ghsvp_wJ_mergeConfig_independent (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (S : Finset W) (a : ↑S -> Bool) (b c : ({v : W // v ∉ S}) -> Bool) :
    wJ (ghsvp_vertexEdges E S) J (fun _ => 0) (ghsvp_mergeConfig S a b) =
      wJ (ghsvp_vertexEdges E S) J (fun _ => 0) (ghsvp_mergeConfig S a c) := by
  unfold wJ
  congr 2
  · apply Finset.sum_congr rfl
    intro e he
    have hins := (Finset.mem_filter.mp he).2
    congr 1
    induction e with
    | h x y =>
      rw [bond_mk, bond_mk]
      have hx : x ∈ S := hins x (by simp)
      have hy : y ∈ S := hins y (by simp)
      change spin (ghsvp_mergeConfig S a b) x * spin (ghsvp_mergeConfig S a b) y =
        spin (ghsvp_mergeConfig S a c) x * spin (ghsvp_mergeConfig S a c) y
      unfold spin
      simp only [ghsvp_mergeConfig, dif_pos hx, dif_pos hy]
  · simp


noncomputable def ghsvp_activeZ (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (S : Finset W) : Real :=
  ∑ a : ↑S -> Bool,
    wJ (ghsvp_vertexEdges E S) J (fun _ => 0)
      (ghsvp_mergeConfig S a (fun _ => false))

@[simp] theorem ghsvp_inactiveConfig_card (S : Finset W) :
    Fintype.card (({v : W // v ∉ S}) -> Bool) =
      2 ^ (Fintype.card W - S.card) := by
  rw [Fintype.card_fun, Fintype.card_subtype_compl]
  simp


theorem ghsvp_vertexZ_eq_inactiveCard_mul_activeZ
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (S : Finset W) :
    ghsvp_vertexZ E J S =
      Fintype.card (({v : W // v ∉ S}) -> Bool) * ghsvp_activeZ E J S := by
  unfold ghsvp_vertexZ ZJ ghsvp_activeZ
  rw [← Equiv.sum_comp (ghsvp_splitConfig S).symm
    (fun s => wJ (ghsvp_vertexEdges E S) J (fun _ => 0) s)]
  simp only [ghsvp_splitConfig, Equiv.coe_fn_symm_mk]
  rw [Fintype.sum_prod_type]
  simp_rw [ghsvp_wJ_mergeConfig_independent E J S _ _ (fun _ => false)]
  simp [Finset.mul_sum]



variable {V : Type*} [Fintype V] [DecidableEq V]


def ghsvp_someSet (A : Finset V) : Finset (Option V) := A.map someEmb


def ghsvp_fieldSet (A : Finset V) : Finset (Option V) := insert none (ghsvp_someSet A)


noncomputable def ghsvp_subsetMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (A : Finset V) : Real :=
  let J2 := ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)
  ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet A) *
    ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_someSet Aᶜ)

lemma ghsvp_someSet_mono : Monotone (ghsvp_someSet : Finset V -> Finset (Option V)) := by
  intro A B hAB
  intro z hz
  rw [ghsvp_someSet, Finset.mem_map] at hz ⊢
  obtain ⟨x, hx, rfl⟩ := hz
  exact ⟨x, hAB hx, rfl⟩

lemma ghsvp_someSet_inter (A B : Finset V) :
    ghsvp_someSet (A ∩ B) = ghsvp_someSet A ∩ ghsvp_someSet B := by
  ext z
  rcases z with _ | z <;> simp [ghsvp_someSet]

lemma ghsvp_someSet_union (A B : Finset V) :
    ghsvp_someSet (A ∪ B) = ghsvp_someSet A ∪ ghsvp_someSet B := by
  ext z
  rcases z with _ | z <;> simp [ghsvp_someSet]

lemma ghsvp_fieldSet_inter (A B : Finset V) :
    ghsvp_fieldSet (A ∩ B) = ghsvp_fieldSet A ∩ ghsvp_fieldSet B := by
  ext z
  rcases z with _ | z <;> simp [ghsvp_fieldSet, ghsvp_someSet]

lemma ghsvp_fieldSet_union (A B : Finset V) :
    ghsvp_fieldSet (A ∪ B) = ghsvp_fieldSet A ∪ ghsvp_fieldSet B := by
  ext z
  rcases z with _ | z <;> simp [ghsvp_fieldSet, ghsvp_someSet]

lemma ghsvp_edgeInside_map_some_iff (A : Finset V) (e : Sym2 V) :
    Sharpness.edgeInside (ghsvp_fieldSet A) (Sym2.map some e) ↔
      Sharpness.edgeInside A e := by
  induction e with
  | h x y => simp [Sharpness.edgeInside, ghsvp_fieldSet, ghsvp_someSet]

lemma ghsvp_origEdges_filter_fieldSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) :
    (FieldGhostDict.origEdges G).filter (Sharpness.edgeInside (ghsvp_fieldSet A)) =
      (ghsvp_vertexEdges G.edgeFinset A).image (Sym2.map some) := by
  rw [FieldGhostDict.origEdges, Finset.filter_image]
  unfold ghsvp_vertexEdges
  congr 1
  ext e
  simp [ghsvp_edgeInside_map_some_iff]

lemma ghsvp_ghostEdges_filter_fieldSet (A : Finset V) :
    (FieldGhostDict.ghostEdges V).filter (Sharpness.edgeInside (ghsvp_fieldSet A)) =
      A.image (fun x => s(some x, none)) := by
  ext e
  induction e with
  | h x y =>
    rcases x with _ | x <;> rcases y with _ | y <;>
      simp [FieldGhostDict.ghostEdges, Sharpness.edgeInside,
        ghsvp_fieldSet, ghsvp_someSet]


theorem ghsvp_fieldSet_couplingSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (A : Finset V) (s : ConfigSpace (Option V)) :
    (∑ e ∈ ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A),
        ghostCoupling (2 * β * h) 1 (fun _ => 2 * β) e * bond s e) =
      (∑ e ∈ ghsvp_vertexEdges G.edgeFinset A,
          (2 * β) * bond (fun x => s (some x)) e) +
        (2 * β * h) * spin s none * ∑ x ∈ A, spin s (some x) := by
  unfold ghsvp_vertexEdges
  rw [FieldGhostDict.withGhost_edgeFinset_eq, Finset.filter_union,
    ghsvp_origEdges_filter_fieldSet, ghsvp_ghostEdges_filter_fieldSet]
  have hdisj : Disjoint
      ((ghsvp_vertexEdges G.edgeFinset A).image (Sym2.map some))
      (A.image (fun x => s(some x, none))) := by
    apply (FieldGhostDict.disjoint_orig_ghost G).mono
    · intro e he
      exact Finset.mem_filter.mp (by
        rw [ghsvp_origEdges_filter_fieldSet]
        exact he) |>.1
    · intro e he
      exact Finset.mem_filter.mp (by
        rw [ghsvp_ghostEdges_filter_fieldSet]
        exact he) |>.1
  rw [Finset.sum_union hdisj]
  congr 1
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro e _
      induction e with
      | h x y =>
        rw [Sym2.map_mk, ghostCoupling_some_some, bond_mk, bond_mk]
        rfl
    · intro a _ b _ hab
      exact Sym2.map.injective (Option.some_injective V) hab
  · rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [ghostCoupling_some_none, bond_mk]
      ring
    · intro a _ b _ hab
      rw [Sym2.eq_iff] at hab
      rcases hab with h | h
      · exact Option.some_injective V h.1
      · exact absurd h.2 (by simp)

theorem ghsvp_fieldSet_weight_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (A : Finset V) (s : ConfigSpace (Option V)) :
    wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
        (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (fun _ => 0) s =
      wJ (ghsvp_vertexEdges G.edgeFinset A) (fun _ => 2 * β)
        (fun x => if x ∈ A then (2 * β * h) * spin s none else 0)
        (fun x => s (some x)) := by
  unfold wJ
  rw [ghsvp_fieldSet_couplingSum]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  congr 2
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.mul_sum]
  simp
  apply Finset.sum_congr rfl
  intro x hx
  rfl

lemma ghsvp_edgeInside_map_someSet_iff (A : Finset V) (e : Sym2 V) :
    Sharpness.edgeInside (ghsvp_someSet A) (Sym2.map some e) ↔
      Sharpness.edgeInside A e := by
  induction e with
  | h x y => simp [Sharpness.edgeInside, ghsvp_someSet]

lemma ghsvp_origEdges_filter_someSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) :
    (FieldGhostDict.origEdges G).filter (Sharpness.edgeInside (ghsvp_someSet A)) =
      (ghsvp_vertexEdges G.edgeFinset A).image (Sym2.map some) := by
  rw [FieldGhostDict.origEdges, Finset.filter_image]
  unfold ghsvp_vertexEdges
  congr 1
  ext e
  simp [ghsvp_edgeInside_map_someSet_iff]

lemma ghsvp_ghostEdges_filter_someSet (A : Finset V) :
    (FieldGhostDict.ghostEdges V).filter (Sharpness.edgeInside (ghsvp_someSet A)) = ∅ := by
  ext e
  induction e with
  | h x y =>
    rcases x with _ | x <;> rcases y with _ | y <;>
      simp [FieldGhostDict.ghostEdges, Sharpness.edgeInside, ghsvp_someSet]

theorem ghsvp_someSet_weight_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (A : Finset V) (s : ConfigSpace (Option V)) :
    wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_someSet A))
        (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (fun _ => 0) s =
      wJ (ghsvp_vertexEdges G.edgeFinset A) (fun _ => 2 * β) (fun _ => 0)
        (fun x => s (some x)) := by
  have hedges :
      ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_someSet A) =
        (ghsvp_vertexEdges G.edgeFinset A).image (Sym2.map some) := by
    unfold ghsvp_vertexEdges
    rw [FieldGhostDict.withGhost_edgeFinset_eq, Finset.filter_union,
      ghsvp_origEdges_filter_someSet, ghsvp_ghostEdges_filter_someSet]
    simp [ghsvp_vertexEdges]
  unfold wJ
  rw [hedges, Finset.sum_image]
  · simp only [zero_mul, Finset.sum_const_zero, add_zero]
    congr 2
    funext e
    induction e with
    | h x y =>
      rw [Sym2.map_mk, ghostCoupling_some_some, bond_mk, bond_mk]
      rfl
  · intro a _ b _ hab
    exact Sym2.map.injective (Option.some_injective V) hab

theorem ghsvp_wJ_negField_flip (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hf : V -> Real) (s : ConfigSpace V) :
    wJ E J (fun x => -hf x) (FieldGhostDict.flipV s) = wJ E J hf s := by
  unfold wJ
  congr 2
  · apply Finset.sum_congr rfl
    intro e he
    rw [FieldGhostDict.bond_flipV]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [FieldGhostDict.spin_flipV]
    ring

theorem ghsvp_ZJ_negField (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hf : V -> Real) : ZJ E J (fun x => -hf x) = ZJ E J hf := by
  unfold ZJ
  rw [← Equiv.sum_comp (FieldGhostDict.flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  apply Finset.sum_congr rfl
  intro s hs
  exact ghsvp_wJ_negField_flip E J hf s


noncomputable def ghsvp_tZ (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (A : Finset V) : Real :=
  ZJ (ghsvp_vertexEdges G.edgeFinset A) (fun _ => 2 * β)
    (fun x => if x ∈ A then 2 * β * h else 0)

noncomputable def ghsvp_uZ (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : Real) (A : Finset V) : Real :=
  ZJ (ghsvp_vertexEdges G.edgeFinset A) (fun _ => 2 * β) (fun _ => 0)

theorem ghsvp_vertexZ_fieldSet_eq_two_mul_tZ
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : Real) (A : Finset V) :
    ghsvp_vertexZ (withGhost G).edgeFinset
        (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (ghsvp_fieldSet A) =
      2 * ghsvp_tZ G β h A := by
  unfold ghsvp_vertexZ ZJ
  rw [FieldGhostDict.sum_option_config, Fintype.sum_bool]
  have htrue :
      (∑ τ : V -> Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
          (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (fun _ => 0)
          (fun z => Option.rec true τ z)) = ghsvp_tZ G β h A := by
    unfold ghsvp_tZ ZJ
    apply Finset.sum_congr rfl
    intro τ hτ
    rw [ghsvp_fieldSet_weight_eq]
    congr 2
    funext x
    simp [FieldGhostDict.split_ghost_spin]
  have hfalse :
      (∑ τ : V -> Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
          (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (fun _ => 0)
          (fun z => Option.rec false τ z)) = ghsvp_tZ G β h A := by
    rw [show (∑ τ : V -> Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A))
          (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (fun _ => 0)
          (fun z => Option.rec false τ z)) =
        ZJ (ghsvp_vertexEdges G.edgeFinset A) (fun _ => 2 * β)
          (fun x => -(if x ∈ A then 2 * β * h else 0)) by
      unfold ZJ
      apply Finset.sum_congr rfl
      intro τ hτ
      rw [ghsvp_fieldSet_weight_eq]
      congr 2
      funext x
      by_cases hx : x ∈ A <;> simp [hx, FieldGhostDict.split_ghost_spin]]
    rw [ghsvp_ZJ_negField]
    rfl
  rw [htrue, hfalse]
  ring

theorem ghsvp_vertexZ_someSet_eq_two_mul_uZ
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : Real) (A : Finset V) :
    ghsvp_vertexZ (withGhost G).edgeFinset
        (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (ghsvp_someSet A) =
      2 * ghsvp_uZ G β A := by
  unfold ghsvp_vertexZ ZJ
  rw [FieldGhostDict.sum_option_config, Fintype.sum_bool]
  have hb : ∀ b : Bool,
      (∑ τ : V -> Bool,
        wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_someSet A))
          (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (fun _ => 0)
          (fun z => Option.rec b τ z)) = ghsvp_uZ G β A := by
    intro b
    unfold ghsvp_uZ ZJ
    apply Finset.sum_congr rfl
    intro τ hτ
    exact ghsvp_someSet_weight_eq G β h A (fun z => Option.rec b τ z)
  rw [hb, hb]
  ring

theorem ghsvp_subsetMass_eq_four_mul_tZ_uZ
    (G : SimpleGraph V) [DecidableRel G.Adj] (β h : Real) (A : Finset V) :
    ghsvp_subsetMass G β h A =
      4 * (ghsvp_tZ G β h A * ghsvp_uZ G β Aᶜ) := by
  unfold ghsvp_subsetMass
  dsimp only
  rw [ghsvp_vertexZ_fieldSet_eq_two_mul_tZ, ghsvp_vertexZ_someSet_eq_two_mul_uZ]
  ring


theorem ghsvp_subsetMass_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (A : Finset V) : 0 <= ghsvp_subsetMass G β h A := by
  unfold ghsvp_subsetMass
  exact mul_nonneg (ZJ_pos _ _ _).le (ZJ_pos _ _ _).le


theorem ghsvp_subsetMass_logSupermodular (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (hβ : 0 <= β) (hh : 0 <= h) (A B : Finset V) :
    ghsvp_subsetMass G β h A * ghsvp_subsetMass G β h B <=
      ghsvp_subsetMass G β h (A ∪ B) * ghsvp_subsetMass G β h (A ∩ B) := by
  let J2 : Sym2 (Option V) -> Real := ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)
  have hJ2 : forall e, 0 <= J2 e := by
    intro e
    induction e with
    | h a b =>
      rcases a with _ | a <;> rcases b with _ | b <;>
        simp [J2, ghostCoupling] <;> positivity
  have hnd : ∀ e ∈ (withGhost G).edgeFinset, ¬ e.IsDiag := by
    intro e he
    exact SimpleGraph.not_isDiag_of_mem_edgeFinset he
  have hp := ghsvp_vertexZ_logSupermodular (withGhost G).edgeFinset J2 hJ2 hnd
    (ghsvp_fieldSet A) (ghsvp_fieldSet B)
  have hz := ghsvp_vertexZ_logSupermodular (withGhost G).edgeFinset J2 hJ2 hnd
    (ghsvp_someSet Aᶜ) (ghsvp_someSet Bᶜ)
  rw [← ghsvp_fieldSet_union, ← ghsvp_fieldSet_inter] at hp
  have hcu : Aᶜ ∪ Bᶜ = (A ∩ B)ᶜ := by ext x; simp
  have hci : Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ := by ext x; simp
  rw [← ghsvp_someSet_union, ← ghsvp_someSet_inter, hcu, hci] at hz
  unfold ghsvp_subsetMass
  change
    (ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet A) *
        ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_someSet Aᶜ)) *
      (ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet B) *
        ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_someSet Bᶜ)) <= _
  have hnon1 : 0 <= ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet (A ∪ B)) :=
    (ZJ_pos _ _ _).le
  have hnon2 : 0 <= ghsvp_vertexZ (withGhost G).edgeFinset J2 (ghsvp_fieldSet (A ∩ B)) :=
    (ZJ_pos _ _ _).le
  have hprod := mul_le_mul hp hz
    (mul_nonneg (ZJ_pos _ _ _).le (ZJ_pos _ _ _).le)
    (mul_nonneg hnon1 hnon2)
  nlinarith [hprod]





noncomputable def ghsvp_disagreementCorr (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : Real) (o x : V) (A : Finset V) : Real :=
  if o ∈ A ∨ x ∈ A then 0
  else ghsvp_vertexCorr G.edgeFinset (fun _ => 2 * β) Aᶜ {o, x}



noncomputable def ghsvp_agreementMag (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (y : V) (A : Finset V) : Real :=
  if y ∈ A then
    ghsvp_vertexCorrField G.edgeFinset (fun _ => 2 * β) (fun _ => 2 * β * h) A {y}
  else 0

theorem ghsvp_disagreementCorr_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : Real) (hβ : 0 <= β) (o x : V) (A : Finset V) :
    0 <= ghsvp_disagreementCorr G β o x A := by
  unfold ghsvp_disagreementCorr
  split_ifs
  · exact le_rfl
  · apply ghsvp_vertexCorr_nonneg
    intro e
    positivity


theorem ghsvp_disagreementCorr_antitone (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : Real) (hβ : 0 <= β) (o x : V) :
    Antitone (ghsvp_disagreementCorr G β o x) := by
  intro A B hAB
  by_cases hA : o ∈ A ∨ x ∈ A
  · have hB : o ∈ B ∨ x ∈ B := hA.elim (fun ho => Or.inl (hAB ho))
      (fun hx => Or.inr (hAB hx))
    simp [ghsvp_disagreementCorr, hA, hB]
  · by_cases hB : o ∈ B ∨ x ∈ B
    · simp only [ghsvp_disagreementCorr, if_pos hB, if_neg hA]
      apply ghsvp_vertexCorr_nonneg
      intro e
      positivity
    · simp only [ghsvp_disagreementCorr, if_neg hA, if_neg hB]
      apply ghsvp_vertexCorr_mono
      · intro e
        positivity
      · exact fun e he => SimpleGraph.not_isDiag_of_mem_edgeFinset he
      · intro v hv
        simp only [Finset.mem_compl] at hv ⊢
        exact fun hvA => hv (hAB hvA)

theorem ghsvp_agreementMag_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (hβ : 0 <= β) (hh : 0 <= h) (y : V) (A : Finset V) :
    0 <= ghsvp_agreementMag G β h y A := by
  unfold ghsvp_agreementMag
  split_ifs
  · apply ghsvp_vertexCorrField_nonneg
    · intro e
      positivity
    · intro v
      positivity
  · exact le_rfl


theorem ghsvp_agreementMag_monotone (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (hβ : 0 <= β) (hh : 0 <= h) (y : V) :
    Monotone (ghsvp_agreementMag G β h y) := by
  intro A B hAB
  by_cases hB : y ∈ B
  · by_cases hA : y ∈ A
    · simp only [ghsvp_agreementMag, if_pos hA, if_pos hB]
      apply ghsvp_vertexCorrField_mono
      · intro e
        positivity
      · intro v
        positivity
      · exact fun e he => SimpleGraph.not_isDiag_of_mem_edgeFinset he
      · exact hAB
    · simp only [ghsvp_agreementMag, if_neg hA, if_pos hB]
      apply ghsvp_vertexCorrField_nonneg
      · intro e
        positivity
      · intro v
        positivity
  · have hA : y ∉ A := fun hy => hB (hAB hy)
    simp [ghsvp_agreementMag, hA, hB]

end StatMech.Ising
