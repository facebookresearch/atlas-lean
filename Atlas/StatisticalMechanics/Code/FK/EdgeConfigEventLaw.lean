/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.EdgeConfigZ











open scoped BigOperators
open SimpleGraph

namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def ecz_closeOff (omega : ConfigSpace (Sym2 V)) : ecz_ClosedOff G :=
  ⟨fun e => if he : e ∈ G.edgeFinset then omega e else false, by
    intro e he
    change (if _ : e ∈ G.edgeFinset then omega e else false) = false
    rw [dif_neg he]⟩

@[simp] theorem ecz_closeOff_apply_edge
    (omega : ConfigSpace (Sym2 V)) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) :
    (ecz_closeOff G omega).1 e = omega e := by
  change (if _ : e ∈ G.edgeFinset then omega e else false) = omega e
  rw [dif_pos he]

@[simp] theorem ecz_closeOff_val (omega : ecz_ClosedOff G) :
    ecz_closeOff G omega.1 = omega := by
  apply Subtype.ext
  funext e
  by_cases he : e ∈ G.edgeFinset
  · change (if _ : e ∈ G.edgeFinset then omega.1 e else false) = omega.1 e
    rw [dif_pos he]
  · change (if _ : e ∈ G.edgeFinset then omega.1 e else false) = omega.1 e
    rw [dif_neg he, omega.2 e he]


def ecz_eventWeight (p q : Real) (A : Set (ecz_ClosedOff G)) : Real :=
  ∑ omega : ecz_ClosedOff G,
    A.indicator (fun omega => fkWeight G p q omega.1) omega



theorem ecz_eventWeight_factorization (p q : Real)
    (A : Set (ecz_ClosedOff G)) :
    (∑ omega : ConfigSpace (Sym2 V),
        (ecz_closeOff G ⁻¹' A).indicator
          (fun omega => fkWeight G p q omega) omega) =
      2 ^ ecz_NE G * ecz_eventWeight G p q A := by
  classical
  set P : Sym2 V → Prop := fun e => e ∈ G.edgeFinset with hP
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm
        (fun omega =>
          (ecz_closeOff G ⁻¹' A).indicator
            (fun omega => fkWeight G p q omega) omega),
      Fintype.sum_prod_type]
  have hcard : Fintype.card ({e // ¬ P e} → Bool) = 2 ^ ecz_NE G := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype]
    rfl
  let edgeConfig : ({e // P e} → Bool) → ecz_ClosedOff G :=
    fun eta => ⟨(Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm
        (eta, fun _ => false), by
      intro e he
      rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg he]⟩
  have hclose : ∀ eta : ({e // P e} → Bool),
      ∀ xi : ({e // ¬ P e} → Bool),
      ecz_closeOff G
          ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (eta, xi)) =
        edgeConfig eta := by
    intro eta xi
    apply Subtype.ext
    funext e
    by_cases he : P e
    · have hedge : e ∈ G.edgeFinset := by simpa [P] using he
      change (if _ : e ∈ G.edgeFinset then
          (Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (eta, xi) e
        else false) =
        (Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm
          (eta, fun _ => false) e
      rw [dif_pos hedge, Equiv.piEquivPiSubtypeProd_symm_apply,
        Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos he, dif_pos he]
    · have hedge : e ∉ G.edgeFinset := by simpa [P] using he
      change (if _ : e ∈ G.edgeFinset then
          (Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (eta, xi) e
        else false) =
        (Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm
          (eta, fun _ => false) e
      rw [dif_neg hedge, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg he]
  have hweight : ∀ eta : ({e // P e} → Bool),
      ∀ xi : ({e // ¬ P e} → Bool),
      fkWeight G p q
          ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (eta, xi)) =
        fkWeight G p q (edgeConfig eta).1 := by
    intro eta xi
    apply ecz_fkWeight_eq_of_edges
    intro e he
    simp [edgeConfig, P, he, Equiv.piEquivPiSubtypeProd_symm_apply]
  have hinner : ∀ eta : ({e // P e} → Bool),
      (∑ xi : ({e // ¬ P e} → Bool),
        (ecz_closeOff G ⁻¹' A).indicator
          (fun omega => fkWeight G p q omega)
          ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (eta, xi))) =
      2 ^ ecz_NE G *
        A.indicator (fun omega => fkWeight G p q omega.1) (edgeConfig eta) := by
    intro eta
    have hterm : ∀ xi : ({e // ¬ P e} → Bool),
        (ecz_closeOff G ⁻¹' A).indicator
          (fun omega => fkWeight G p q omega)
          ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (eta, xi)) =
        A.indicator (fun omega => fkWeight G p q omega.1)
          (edgeConfig eta) := by
      intro xi
      by_cases hA : edgeConfig eta ∈ A
      · have hpre :
            (Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm
                (eta, xi) ∈ ecz_closeOff G ⁻¹' A := by
          change ecz_closeOff G
              ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm
                (eta, xi)) ∈ A
          rwa [hclose eta xi]
        rw [Set.indicator_of_mem hA, Set.indicator_of_mem hpre]
        exact hweight eta xi
      · have hpre :
            (Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm
                (eta, xi) ∉ ecz_closeOff G ⁻¹' A := by
          change ecz_closeOff G
              ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm
                (eta, xi)) ∉ A
          rwa [hclose eta xi]
        rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hpre]
    rw [Finset.sum_congr rfl (fun xi _ => hterm xi),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    push_cast
    rfl
  rw [Finset.sum_congr rfl (fun eta _ => hinner eta), ← Finset.mul_sum]
  congr 1
  unfold ecz_eventWeight
  symm
  refine Finset.sum_nbij'
    (i := fun omega : ecz_ClosedOff G =>
      (fun e : {e // P e} => omega.1 e.1))
    (j := edgeConfig)
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro omega _
    apply Subtype.ext
    funext e
    by_cases he : P e
    · simp [edgeConfig, he, Equiv.piEquivPiSubtypeProd_symm_apply]
    · simp [edgeConfig, he, Equiv.piEquivPiSubtypeProd_symm_apply,
        omega.2 e he]
  · intro eta _
    funext e
    simp [edgeConfig, e.2, Equiv.piEquivPiSubtypeProd_symm_apply]
  · intro omega _
    have hj : edgeConfig (fun e : {e // P e} => omega.1 e.1) = omega := by
      apply Subtype.ext
      funext e
      by_cases he : P e
      · simp [edgeConfig, he, Equiv.piEquivPiSubtypeProd_symm_apply]
      · simp [edgeConfig, he, Equiv.piEquivPiSubtypeProd_symm_apply,
          omega.2 e he]
    rw [hj]



theorem ecz_eventProb_eq (p q : Real) (A : Set (ecz_ClosedOff G)) :
    (∑ omega : ConfigSpace (Sym2 V),
        (ecz_closeOff G ⁻¹' A).indicator (fun _ => (1 : Real)) omega *
          fkProb G p q omega) =
      ecz_eventWeight G p q A / ecz_fkZEdge G p q := by
  unfold fkProb
  calc
    (∑ omega : ConfigSpace (Sym2 V),
        (ecz_closeOff G ⁻¹' A).indicator (fun _ => (1 : Real)) omega *
          (fkWeight G p q omega / fkZ G p q)) =
      ∑ omega : ConfigSpace (Sym2 V),
        (ecz_closeOff G ⁻¹' A).indicator
          (fun omega => fkWeight G p q omega) omega / fkZ G p q := by
      apply Finset.sum_congr rfl
      intro omega _
      by_cases hA : omega ∈ ecz_closeOff G ⁻¹' A
      · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA]
        ring
      · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]
        ring
    _ = (∑ omega : ConfigSpace (Sym2 V),
        (ecz_closeOff G ⁻¹' A).indicator
          (fun omega => fkWeight G p q omega) omega) / fkZ G p q := by
      rw [Finset.sum_div]
    _ = ecz_eventWeight G p q A / ecz_fkZEdge G p q := by
      rw [ecz_eventWeight_factorization G p q A,
        ecz_factorization G p q]
      have htwo : (2 : Real) ^ ecz_NE G ≠ 0 := by positivity
      field_simp

end

end StatMech.FK
