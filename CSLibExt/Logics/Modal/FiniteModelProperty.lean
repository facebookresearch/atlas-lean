/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.Filtration

@[expose] public section

/-!
# The finite model property and decidability of T, S4 and S5

`Filtration.lean` proves the finite model property and decidability of K with the smallest
filtration. For T, S4 and S5 the filtered model must also satisfy the frame condition, which
needs a different filtration relation for S4 and S5 (Blackburn–de Rijke–Venema §2.3).

It applies the filtration lemma for any filtration relation (`IsFiltration`,
`satisfies_finModel_filtrationWorlds_iff`, in `Filtration.lean`) to three relations:

* `filtrationRel`, the smallest filtration. Any filtration of a reflexive model is reflexive
  (`finRefl_of_isFiltration`).
* `lemmonRel`: `s R t` iff every `□ψ ∈ Σ ∩ s` has `□ψ ∈ t` and `ψ ∈ t` (the `□` form of BdRV's
  `R^t`, Lemma 2.42). It is a filtration of any transitive model, and it is always transitive.
* `s5Rel`: `s R t` iff `s` and `t` contain the same boxed formulas of `Σ`. It is a filtration of
  any equivalence model, and an equivalence.
* `exists_finite_countermodel_T`, `_S4`, `_S5` (**finite model property**): a non-theorem fails
  in a model of the class with at most `2 ^ |sub φ|` worlds.
* `instDecidablePredDerivableT`, `_S4`, `_S5`: **T-, S4- and S5-provability are decidable**, by
  enumerating the finitely many models on subsets of `sub φ` whose relation satisfies the frame
  condition (decidability proofs, not practical decision procedures).

## References

* P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, Cambridge University Press, 2001,
  §2.3 (Definition 2.36, Lemma 2.42 with Exercise 2.3.5) and §6.2 (Definition 6.6,
  Theorem 6.7).
* E. J. Lemmon, D. Scott, *An Introduction to Modal Logic*, Blackwell, 1977.
-/

namespace Cslib
namespace Modal

universe u v

variable {Atom : Type u} [DecidableEq Atom]

/-! ### The filtration lemma for any filtration -/

section GeneralFiltration

variable {World : Type v} (M : KripkeModel World Atom) (phi : Formula Atom)

/-- A filtration of a model refutes a formula that the model refutes, with at most `2 ^ |sub φ|`
worlds. -/
theorem not_valid_finModel_of_isFiltration
    {R : Finset (Finset (Formula Atom) × Finset (Formula Atom))} (hR : IsFiltration M phi R)
    {w : World} (hw : ¬M.Satisfies w phi) :
    ¬(finModel (filtrationWorlds M phi) R (filtrationWorlds_nonempty M phi)).Valid phi :=
  fun hval ↦ hw ((satisfies_finModel_filtrationWorlds_iff M phi hR (Formula.mem_sub_self phi) w).mp
    (hval _))

end GeneralFiltration

/-! ### The Lemmon and S5 filtrations -/

section Relations

variable {World : Type v} (M : KripkeModel World Atom) (phi : Formula Atom)

/-- The Lemmon (transitive) filtration relation: `s R t` iff every `□ψ ∈ sub φ` in `s` has
`□ψ ∈ t` and `ψ ∈ t`. This is the `□` form of Blackburn–de Rijke–Venema's `R^t` (Lemma 2.42). -/
noncomputable def lemmonRel : Finset (Finset (Formula Atom) × Finset (Formula Atom)) := by
  classical exact (filtrationWorlds M phi ×ˢ filtrationWorlds M phi).filter fun st ↦
    ∀ psi, Formula.box psi ∈ phi.sub → Formula.box psi ∈ st.1 →
      Formula.box psi ∈ st.2 ∧ psi ∈ st.2

/-- The S5 filtration relation: `s R t` iff `s` and `t` contain the same boxed formulas of
`sub φ`. -/
noncomputable def s5Rel : Finset (Finset (Formula Atom) × Finset (Formula Atom)) := by
  classical exact (filtrationWorlds M phi ×ˢ filtrationWorlds M phi).filter fun st ↦
    ∀ psi, Formula.box psi ∈ phi.sub → (Formula.box psi ∈ st.1 ↔ Formula.box psi ∈ st.2)

theorem mem_lemmonRel {s t : Finset (Formula Atom)} (hs : s ∈ filtrationWorlds M phi)
    (ht : t ∈ filtrationWorlds M phi) :
    (s, t) ∈ lemmonRel M phi ↔ ∀ psi, Formula.box psi ∈ phi.sub → Formula.box psi ∈ s →
      Formula.box psi ∈ t ∧ psi ∈ t := by
  classical
  simp [lemmonRel, hs, ht]

theorem mem_s5Rel {s t : Finset (Formula Atom)} (hs : s ∈ filtrationWorlds M phi)
    (ht : t ∈ filtrationWorlds M phi) :
    (s, t) ∈ s5Rel M phi ↔
      ∀ psi, Formula.box psi ∈ phi.sub → (Formula.box psi ∈ s ↔ Formula.box psi ∈ t) := by
  classical
  simp [s5Rel, hs, ht]

/-- The Lemmon relation is a filtration of every transitive model. -/
theorem isFiltration_lemmonRel (htrans : ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) :
    IsFiltration M phi (lemmonRel M phi) where
  min {w v} hwv := by
    rw [mem_lemmonRel M phi (subType_mem_filtrationWorlds M phi w)
      (subType_mem_filtrationWorlds M phi v)]
    intro psi hpsi hbox
    have hw := ((mem_subType M phi).mp hbox).2
    exact ⟨(mem_subType M phi).mpr ⟨hpsi, fun u hvu ↦ hw u (htrans hwv hvu)⟩,
      (mem_subType M phi).mpr ⟨Formula.mem_sub_of_box_mem hpsi, hw v hwv⟩⟩
  max {w v} hrel psi hpsi hbox := by
    rw [mem_lemmonRel M phi (subType_mem_filtrationWorlds M phi w)
      (subType_mem_filtrationWorlds M phi v)] at hrel
    exact ((mem_subType M phi).mp (hrel psi hpsi ((mem_subType M phi).mpr ⟨hpsi, hbox⟩)).2).2

/-- The S5 relation is a filtration of every model whose relation is an equivalence. -/
theorem isFiltration_s5Rel (hequiv : Equivalence M.rel) : IsFiltration M phi (s5Rel M phi) where
  min {w v} hwv := by
    rw [mem_s5Rel M phi (subType_mem_filtrationWorlds M phi w)
      (subType_mem_filtrationWorlds M phi v)]
    intro psi hpsi
    rw [mem_subType, mem_subType]
    refine and_congr_right fun _ ↦ ⟨fun h u hvu ↦ h u (hequiv.trans hwv hvu),
      fun h u hwu ↦ h u (hequiv.trans (hequiv.symm hwv) hwu)⟩
  max {w v} hrel psi hpsi hbox := by
    rw [mem_s5Rel M phi (subType_mem_filtrationWorlds M phi w)
      (subType_mem_filtrationWorlds M phi v)] at hrel
    have hv := ((mem_subType M phi).mp ((hrel psi hpsi).mp
      ((mem_subType M phi).mpr ⟨hpsi, hbox⟩))).2
    exact hv v (hequiv.refl v)

end Relations

/-! ### Frame conditions on finite models -/

/-- `R` is reflexive on `U`. -/
def FinRefl (U : Finset (Finset (Formula Atom)))
    (R : Finset (Finset (Formula Atom) × Finset (Formula Atom))) : Prop :=
  ∀ s ∈ U, (s, s) ∈ R

/-- `R` is transitive on `U`. -/
def FinTrans (U : Finset (Finset (Formula Atom)))
    (R : Finset (Finset (Formula Atom) × Finset (Formula Atom))) : Prop :=
  ∀ s ∈ U, ∀ t ∈ U, ∀ r ∈ U, (s, t) ∈ R → (t, r) ∈ R → (s, r) ∈ R

/-- `R` is symmetric on `U`. -/
def FinSymm (U : Finset (Finset (Formula Atom)))
    (R : Finset (Finset (Formula Atom) × Finset (Formula Atom))) : Prop :=
  ∀ s ∈ U, ∀ t ∈ U, (s, t) ∈ R → (t, s) ∈ R

instance (U : Finset (Finset (Formula Atom)))
    (R : Finset (Finset (Formula Atom) × Finset (Formula Atom))) : Decidable (FinRefl U R) := by
  unfold FinRefl; infer_instance

instance (U : Finset (Finset (Formula Atom)))
    (R : Finset (Finset (Formula Atom) × Finset (Formula Atom))) : Decidable (FinTrans U R) := by
  unfold FinTrans; infer_instance

instance (U : Finset (Finset (Formula Atom)))
    (R : Finset (Finset (Formula Atom) × Finset (Formula Atom))) : Decidable (FinSymm U R) := by
  unfold FinSymm; infer_instance

section FinModelFrame

variable {U : Finset (Finset (Formula Atom))}
  {R : Finset (Finset (Formula Atom) × Finset (Formula Atom))} (hU : U.Nonempty)

omit [DecidableEq Atom] in
theorem finModel_refl (h : FinRefl U R) (s : {s // s ∈ U}) : (finModel U R hU).rel s s :=
  h s.1 s.2

omit [DecidableEq Atom] in
theorem finModel_trans (h : FinTrans U R) {a b c : {s // s ∈ U}} (hab : (finModel U R hU).rel a b)
    (hbc : (finModel U R hU).rel b c) : (finModel U R hU).rel a c :=
  h a.1 a.2 b.1 b.2 c.1 c.2 hab hbc

omit [DecidableEq Atom] in
theorem finModel_equivalence (hr : FinRefl U R) (hs : FinSymm U R) (ht : FinTrans U R) :
    Equivalence (finModel U R hU).rel :=
  ⟨finModel_refl hU hr, fun {a b} h ↦ hs a.1 a.2 b.1 b.2 h, finModel_trans hU ht⟩

end FinModelFrame

/-! ### Frame properties of the filtrations -/

section FiltrationFrames

variable {World : Type v} (M : KripkeModel World Atom) (phi : Formula Atom)

/-- Any filtration of a reflexive model is reflexive. -/
theorem finRefl_of_isFiltration {R : Finset (Finset (Formula Atom) × Finset (Formula Atom))}
    (hR : IsFiltration M phi R) (hrefl : ∀ w, M.rel w w) : FinRefl (filtrationWorlds M phi) R :=
  fun s hs ↦ by
    obtain ⟨w, rfl⟩ := exists_subType_eq M phi hs
    exact hR.min (hrefl w)

theorem finTrans_lemmonRel : FinTrans (filtrationWorlds M phi) (lemmonRel M phi) :=
  fun s hs t ht r hr hst htr ↦ by
    rw [mem_lemmonRel M phi hs ht] at hst
    rw [mem_lemmonRel M phi ht hr] at htr
    rw [mem_lemmonRel M phi hs hr]
    exact fun psi hpsi hbox ↦ htr psi hpsi (hst psi hpsi hbox).1

theorem finSymm_s5Rel : FinSymm (filtrationWorlds M phi) (s5Rel M phi) :=
  fun s hs t ht hst ↦ by
    rw [mem_s5Rel M phi hs ht] at hst
    rw [mem_s5Rel M phi ht hs]
    exact fun psi hpsi ↦ (hst psi hpsi).symm

theorem finTrans_s5Rel : FinTrans (filtrationWorlds M phi) (s5Rel M phi) :=
  fun s hs t ht r hr hst htr ↦ by
    rw [mem_s5Rel M phi hs ht] at hst
    rw [mem_s5Rel M phi ht hr] at htr
    rw [mem_s5Rel M phi hs hr]
    exact fun psi hpsi ↦ (hst psi hpsi).trans (htr psi hpsi)

end FiltrationFrames

/-! ### Finite model property -/

section FMP

omit [DecidableEq Atom] in
theorem card_le_of_card_finset_le {s : Finset (Finset (Formula Atom))} {n : ℕ}
    (h : s.card ≤ n) : Fintype.card {x // x ∈ s} ≤ n := by
  rw [Fintype.card_coe]
  exact h

variable {phi : Formula Atom}

omit [DecidableEq Atom] in
theorem exists_not_satisfies_of_not_derivable_T (h : ¬Derivable Axioms.T phi) :
    ∃ (W : Type u) (M : KripkeModel W Atom) (w : W), (∀ w, M.rel w w) ∧ ¬M.Satisfies w phi := by
  by_contra hall
  push Not at hall
  exact h (derivable_T_iff.mpr fun W M hrefl w ↦ hall W M w hrefl)

omit [DecidableEq Atom] in
theorem exists_not_satisfies_of_not_derivable_S4 (h : ¬Derivable Axioms.S4 phi) :
    ∃ (W : Type u) (M : KripkeModel W Atom) (w : W), ((∀ w, M.rel w w) ∧
      ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) ∧ ¬M.Satisfies w phi := by
  by_contra hall
  push Not at hall
  exact h (derivable_S4_iff.mpr fun W M hrefl htrans w ↦ hall W M w ⟨hrefl, htrans⟩)

omit [DecidableEq Atom] in
theorem exists_not_satisfies_of_not_derivable_S5 (h : ¬Derivable Axioms.S5 phi) :
    ∃ (W : Type u) (M : KripkeModel W Atom) (w : W), Equivalence M.rel ∧ ¬M.Satisfies w phi := by
  by_contra hall
  push Not at hall
  exact h (derivable_S5_iff.mpr fun W M hequiv w ↦ hall W M w hequiv)

/-- **Finite model property of T**: a non-theorem fails in a reflexive model with at most
`2 ^ |sub φ|` worlds. -/
theorem exists_finite_countermodel_T (h : ¬Derivable Axioms.T phi) :
    ∃ (W : Type u) (_ : Fintype W) (M : KripkeModel W Atom),
      Fintype.card W ≤ 2 ^ phi.sub.card ∧ (∀ w, M.rel w w) ∧ ¬M.Valid phi := by
  obtain ⟨W, M, w, hrefl, hw⟩ := exists_not_satisfies_of_not_derivable_T h
  have hR := isFiltration_filtrationRel M phi
  refine ⟨_, inferInstance, _, ?_, finModel_refl _ (finRefl_of_isFiltration M phi hR hrefl),
    not_valid_finModel_of_isFiltration M phi hR hw⟩
  exact card_le_of_card_finset_le (card_filtrationWorlds_le M phi)

/-- **Finite model property of S4**: a non-theorem fails in a reflexive transitive model with at
most `2 ^ |sub φ|` worlds. -/
theorem exists_finite_countermodel_S4 (h : ¬Derivable Axioms.S4 phi) :
    ∃ (W : Type u) (_ : Fintype W) (M : KripkeModel W Atom),
      Fintype.card W ≤ 2 ^ phi.sub.card ∧ ((∀ w, M.rel w w) ∧
        ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) ∧ ¬M.Valid phi := by
  obtain ⟨W, M, w, ⟨hrefl, htrans⟩, hw⟩ := exists_not_satisfies_of_not_derivable_S4 h
  have hR := isFiltration_lemmonRel M phi htrans
  refine ⟨_, inferInstance, _, ?_, ⟨finModel_refl _ (finRefl_of_isFiltration M phi hR hrefl),
    finModel_trans _ (finTrans_lemmonRel M phi)⟩, not_valid_finModel_of_isFiltration M phi hR hw⟩
  exact card_le_of_card_finset_le (card_filtrationWorlds_le M phi)

/-- **Finite model property of S5**: a non-theorem fails in an equivalence model with at most
`2 ^ |sub φ|` worlds. -/
theorem exists_finite_countermodel_S5 (h : ¬Derivable Axioms.S5 phi) :
    ∃ (W : Type u) (_ : Fintype W) (M : KripkeModel W Atom),
      Fintype.card W ≤ 2 ^ phi.sub.card ∧ Equivalence M.rel ∧ ¬M.Valid phi := by
  obtain ⟨W, M, w, hequiv, hw⟩ := exists_not_satisfies_of_not_derivable_S5 h
  have hR := isFiltration_s5Rel M phi hequiv
  refine ⟨_, inferInstance, _, ?_, finModel_equivalence _
    (finRefl_of_isFiltration M phi hR hequiv.refl) (finSymm_s5Rel M phi) (finTrans_s5Rel M phi),
    not_valid_finModel_of_isFiltration M phi hR hw⟩
  exact card_le_of_card_finset_le (card_filtrationWorlds_le M phi)

end FMP

/-! ### Decidability -/

section Decidability

/-- The finite check for a frame condition `C`: `φ` holds in every model on a nonempty set `U` of
subsets of `sub φ`, for every relation `R ⊆ U × U` satisfying `C`. -/
def FinValidWith (C : Finset (Finset (Formula Atom)) →
    Finset (Finset (Formula Atom) × Finset (Formula Atom)) → Prop) (phi : Formula Atom) : Prop :=
  ∀ U ∈ phi.sub.powerset.powerset, U.Nonempty → ∀ R ∈ (U ×ˢ U).powerset, C U R → ∀ s ∈ U,
    evalFin U R s phi = true

instance (C : Finset (Finset (Formula Atom)) →
    Finset (Finset (Formula Atom) × Finset (Formula Atom)) → Prop) [∀ U R, Decidable (C U R)]
    (phi : Formula Atom) : Decidable (FinValidWith C phi) := by
  unfold FinValidWith
  infer_instance

/-- The filtration data `(filtrationWorlds, R)` is among the finitely many models checked. -/
theorem finValidWith_apply {C : Finset (Finset (Formula Atom)) →
    Finset (Finset (Formula Atom) × Finset (Formula Atom)) → Prop} {phi : Formula Atom}
    (h : FinValidWith C phi) {World : Type v} (M : KripkeModel World Atom)
    {R : Finset (Finset (Formula Atom) × Finset (Formula Atom))}
    (hRsub : R ⊆ filtrationWorlds M phi ×ˢ filtrationWorlds M phi)
    (hC : C (filtrationWorlds M phi) R) :
    (finModel (filtrationWorlds M phi) R (filtrationWorlds_nonempty M phi)).Valid phi := by
  intro s
  have hU : filtrationWorlds M phi ∈ phi.sub.powerset.powerset := by
    classical
    simp only [Finset.mem_powerset]
    exact Finset.filter_subset _ _
  exact (satisfies_finModel_iff _ _ _ s phi).mpr
    (h _ hU (filtrationWorlds_nonempty M phi) R (Finset.mem_powerset.mpr hRsub) hC s.1 s.2)

theorem lemmonRel_subset {World : Type v} (M : KripkeModel World Atom) (phi : Formula Atom) :
    lemmonRel M phi ⊆ filtrationWorlds M phi ×ˢ filtrationWorlds M phi := by
  classical
  exact Finset.filter_subset _ _

theorem s5Rel_subset {World : Type v} (M : KripkeModel World Atom) (phi : Formula Atom) :
    s5Rel M phi ⊆ filtrationWorlds M phi ×ˢ filtrationWorlds M phi := by
  classical
  exact Finset.filter_subset _ _

theorem filtrationRel_subset {World : Type v} (M : KripkeModel World Atom) (phi : Formula Atom) :
    filtrationRel M phi ⊆ filtrationWorlds M phi ×ˢ filtrationWorlds M phi := by
  classical
  exact Finset.filter_subset _ _

variable {phi : Formula Atom}

/-- `φ` is a T-theorem iff it holds in every reflexive model on subsets of `sub φ`. -/
theorem derivable_T_iff_finValidWith : Derivable Axioms.T phi ↔ FinValidWith FinRefl phi := by
  constructor
  · intro h U _ hU R _ hrefl s hs
    exact (satisfies_finModel_iff U R hU ⟨s, hs⟩ phi).mp
      (h.valid_T (finModel_refl hU hrefl) _)
  · intro h
    by_contra hd
    obtain ⟨W, M, w, hrefl, hw⟩ := exists_not_satisfies_of_not_derivable_T hd
    have hR := isFiltration_filtrationRel M phi
    exact not_valid_finModel_of_isFiltration M phi hR hw
      (finValidWith_apply h M (filtrationRel_subset M phi) (finRefl_of_isFiltration M phi hR hrefl))

/-- `φ` is an S4-theorem iff it holds in every reflexive transitive model on subsets of
`sub φ`. -/
theorem derivable_S4_iff_finValidWith :
    Derivable Axioms.S4 phi ↔ FinValidWith (fun U R ↦ FinRefl U R ∧ FinTrans U R) phi := by
  constructor
  · intro h U _ hU R _ hC s hs
    exact (satisfies_finModel_iff U R hU ⟨s, hs⟩ phi).mp
      (h.valid_S4 (finModel_refl hU hC.1) (finModel_trans hU hC.2) _)
  · intro h
    by_contra hd
    obtain ⟨W, M, w, ⟨hrefl, htrans⟩, hw⟩ := exists_not_satisfies_of_not_derivable_S4 hd
    have hR := isFiltration_lemmonRel M phi htrans
    exact not_valid_finModel_of_isFiltration M phi hR hw
      (finValidWith_apply h M (lemmonRel_subset M phi)
        ⟨finRefl_of_isFiltration M phi hR hrefl, finTrans_lemmonRel M phi⟩)

/-- `φ` is an S5-theorem iff it holds in every equivalence model on subsets of `sub φ`. -/
theorem derivable_S5_iff_finValidWith :
    Derivable Axioms.S5 phi ↔
      FinValidWith (fun U R ↦ FinRefl U R ∧ FinSymm U R ∧ FinTrans U R) phi := by
  constructor
  · intro h U _ hU R _ hC s hs
    exact (satisfies_finModel_iff U R hU ⟨s, hs⟩ phi).mp
      (h.valid_S5 (finModel_equivalence hU hC.1 hC.2.1 hC.2.2) _)
  · intro h
    by_contra hd
    obtain ⟨W, M, w, hequiv, hw⟩ := exists_not_satisfies_of_not_derivable_S5 hd
    have hR := isFiltration_s5Rel M phi hequiv
    exact not_valid_finModel_of_isFiltration M phi hR hw
      (finValidWith_apply h M (s5Rel_subset M phi)
        ⟨finRefl_of_isFiltration M phi hR hequiv.refl, finSymm_s5Rel M phi, finTrans_s5Rel M phi⟩)

/-- **Decidability of T.** -/
instance instDecidablePredDerivableT : DecidablePred (Derivable (Axioms.T : Set (Formula Atom))) :=
  fun _ ↦ decidable_of_iff _ derivable_T_iff_finValidWith.symm

/-- **Decidability of S4.** -/
instance instDecidablePredDerivableS4 :
    DecidablePred (Derivable (Axioms.S4 : Set (Formula Atom))) :=
  fun _ ↦ decidable_of_iff _ derivable_S4_iff_finValidWith.symm

/-- **Decidability of S5.** -/
instance instDecidablePredDerivableS5 :
    DecidablePred (Derivable (Axioms.S5 : Set (Formula Atom))) :=
  fun _ ↦ decidable_of_iff _ derivable_S5_iff_finValidWith.symm

end Decidability

end Modal
end Cslib
