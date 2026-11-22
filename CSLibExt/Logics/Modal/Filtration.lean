/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.Canonical
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Prod

@[expose] public section

/-!
# Filtration, the finite model property and decidability of K

`Formula.sub φ` is the finite set of subformulas of `φ`. The **filtration** of a Kripke model `M`
through `Σ = sub φ` identifies worlds that satisfy the same formulas of `Σ`. Its worlds are the
`Σ`-types `{ψ ∈ Σ | M, w ⊨ ψ}` that occur in `M`. It relates two types when some worlds of those
types are related in `M` (the smallest filtration), and makes an atom of `Σ` true at a type when
the type contains it.

* `satisfies_finModel_filtrationWorlds_iff` (**filtration lemma**): for any filtration relation
  `R` (`IsFiltration`) and `ψ ∈ Σ = sub φ`, `ψ` holds at the type of `w` in the finite model iff it
  holds at `w` in `M`. `satisfies_filtration_iff` is the case of the smallest filtration, which is
  what K needs; `FiniteModelProperty.lean` uses other filtrations for T, S4 and S5.
* `exists_finite_countermodel` (**finite model property**): a formula that is not a K-theorem fails
  in a Kripke model with at most `2 ^ |sub φ|` worlds.
* `derivable_K_iff_forall_finModel`: `φ` is a K-theorem iff it holds in every model on a nonempty
  set `U` of subsets of `sub φ`, with any relation `R` (pairs outside `U × U` are ignored) and the
  valuation "an atom is true at `s` iff it belongs to `s`". Up to the irrelevant pairs there are
  finitely many such models, and satisfaction in them is computed by `evalFin`.
* `instDecidablePredDerivableK`: **K-provability is decidable** (for atoms with decidable
  equality). The procedure enumerates all such models; it is a decidability proof, not a practical
  decision procedure.

## References

* P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, Cambridge University Press, 2001,
  §2.3 (filtrations, Definition 2.36) and §6.2 (decidability via the finite model property,
  Definition 6.6 and Theorem 6.7).
-/

namespace Cslib
namespace Modal

universe u v

variable {Atom : Type u}

variable [DecidableEq Atom]

namespace Formula

/-- The subformulas of a formula, including itself. -/
def sub : Formula Atom → Finset (Formula Atom)
  | .atom p => {.atom p}
  | .bot => {.bot}
  | .imp phi psi => insert (.imp phi psi) (sub phi ∪ sub psi)
  | .box phi => insert (.box phi) (sub phi)

theorem mem_sub_self (phi : Formula Atom) : phi ∈ phi.sub := by
  cases phi <;> simp [sub]

/-- Subformula is transitive. -/
theorem sub_subset_of_mem {phi psi : Formula Atom} (h : psi ∈ phi.sub) : psi.sub ⊆ phi.sub := by
  induction phi with
  | atom p => simp only [sub, Finset.mem_singleton] at h; subst h; rfl
  | bot => simp only [sub, Finset.mem_singleton] at h; subst h; rfl
  | imp a b iha ihb =>
    simp only [sub, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · rfl
    · exact (iha h).trans (by intro x hx; simp [sub, hx])
    · exact (ihb h).trans (by intro x hx; simp [sub, hx])
  | box a iha =>
    simp only [sub, Finset.mem_insert] at h
    rcases h with rfl | h
    · rfl
    · exact (iha h).trans (by intro x hx; simp [sub, hx])

theorem mem_sub_of_imp_mem_left {phi a b : Formula Atom} (h : imp a b ∈ phi.sub) : a ∈ phi.sub :=
  sub_subset_of_mem h (by simp [sub, mem_sub_self])

theorem mem_sub_of_imp_mem_right {phi a b : Formula Atom} (h : imp a b ∈ phi.sub) :
    b ∈ phi.sub :=
  sub_subset_of_mem h (by simp [sub, mem_sub_self])

theorem mem_sub_of_box_mem {phi a : Formula Atom} (h : box a ∈ phi.sub) : a ∈ phi.sub :=
  sub_subset_of_mem h (by simp [sub, mem_sub_self])

end Formula

/-! ### Finite models on sets of subformulas -/

/-- The Kripke model on a nonempty finite set `U` of sets of formulas, with relation `R` and an atom
true at `s` iff it belongs to `s`. -/
def finModel (U : Finset (Finset (Formula Atom))) (R : Finset (Finset (Formula Atom) ×
    Finset (Formula Atom))) (hU : U.Nonempty) : KripkeModel {s // s ∈ U} Atom where
  nonempty_world := let ⟨s, hs⟩ := hU; ⟨⟨s, hs⟩⟩
  rel s t := (s.1, t.1) ∈ R
  valuation s p := Formula.atom p ∈ s.1

/-- Satisfaction in `finModel U R`, computed by recursion on the formula. -/
def evalFin (U : Finset (Finset (Formula Atom))) (R : Finset (Finset (Formula Atom) ×
    Finset (Formula Atom))) (s : Finset (Formula Atom)) : Formula Atom → Bool
  | .atom p => decide (Formula.atom p ∈ s)
  | .bot => false
  | .imp phi psi => !evalFin U R s phi || evalFin U R s psi
  | .box phi => decide (∀ t ∈ U, (s, t) ∈ R → evalFin U R t phi = true)

theorem satisfies_finModel_iff (U : Finset (Finset (Formula Atom)))
    (R : Finset (Finset (Formula Atom) × Finset (Formula Atom))) (hU : U.Nonempty)
    (s : {s // s ∈ U}) (phi : Formula Atom) :
    (finModel U R hU).Satisfies s phi ↔ evalFin U R s.1 phi = true := by
  induction phi generalizing s with
  | atom p => simp [finModel, evalFin]
  | bot => simp [evalFin]
  | imp phi psi ih₁ ih₂ =>
    rw [KripkeModel.satisfies_imp, ih₁, ih₂, evalFin]
    cases evalFin U R s.1 phi <;> simp
  | box phi ih =>
    rw [KripkeModel.satisfies_box, evalFin, decide_eq_true_iff]
    constructor
    · intro h t ht hst
      exact (ih ⟨t, ht⟩).mp (h ⟨t, ht⟩ hst)
    · intro h t hst
      exact (ih t).mpr (h t.1 t.2 hst)

/-! ### Filtration -/

section Filtration

variable {World : Type v} (M : KripkeModel World Atom) (phi : Formula Atom)

/-- The `Σ`-type of a world: the subformulas of `φ` it satisfies. -/
noncomputable def subType (w : World) : Finset (Formula Atom) := by
  classical exact phi.sub.filter fun psi ↦ M.Satisfies w psi

theorem mem_subType {w : World} {psi : Formula Atom} :
    psi ∈ subType M phi w ↔ psi ∈ phi.sub ∧ M.Satisfies w psi := by
  classical
  simp [subType]

/-- The `Σ`-types that occur in `M`. -/
noncomputable def filtrationWorlds : Finset (Finset (Formula Atom)) := by
  classical exact phi.sub.powerset.filter fun s ↦ ∃ w, subType M phi w = s

/-- The smallest filtration relation: two types are related when some worlds of those types are
related in `M`. -/
noncomputable def filtrationRel : Finset (Finset (Formula Atom) × Finset (Formula Atom)) := by
  classical exact (filtrationWorlds M phi ×ˢ filtrationWorlds M phi).filter fun st ↦
    ∃ w w', subType M phi w = st.1 ∧ subType M phi w' = st.2 ∧ M.rel w w'

theorem subType_mem_filtrationWorlds (w : World) : subType M phi w ∈ filtrationWorlds M phi := by
  classical
  simp only [filtrationWorlds, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun psi h ↦ ((mem_subType M phi).mp h).1, w, rfl⟩

theorem filtrationWorlds_nonempty : (filtrationWorlds M phi).Nonempty :=
  let ⟨w⟩ := M.nonempty_world
  ⟨_, subType_mem_filtrationWorlds M phi w⟩

theorem mem_filtrationRel {s t : Finset (Formula Atom)} :
    (s, t) ∈ filtrationRel M phi ↔
      ∃ w w', subType M phi w = s ∧ subType M phi w' = t ∧ M.rel w w' := by
  classical
  simp only [filtrationRel, Finset.mem_filter, Finset.mem_product]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨⟨?_, ?_⟩, h⟩⟩
  · obtain ⟨w, _, rfl, _⟩ := h
    exact subType_mem_filtrationWorlds M phi w
  · obtain ⟨_, w', _, rfl, _⟩ := h
    exact subType_mem_filtrationWorlds M phi w'

/-- Every type in `filtrationWorlds` is the type of a world. -/
theorem exists_subType_eq {s : Finset (Formula Atom)} (hs : s ∈ filtrationWorlds M phi) :
    ∃ w, subType M phi w = s := by
  classical
  simp only [filtrationWorlds, Finset.mem_filter] at hs
  exact hs.2

/-- Worlds of the same type agree on the formulas of `sub φ`. -/
theorem satisfies_iff_of_subType_eq {w v : World} (h : subType M phi w = subType M phi v)
    {psi : Formula Atom} (hpsi : psi ∈ phi.sub) : M.Satisfies w psi ↔ M.Satisfies v psi := by
  constructor
  · intro hw
    have : psi ∈ subType M phi v := h ▸ (mem_subType M phi).mpr ⟨hpsi, hw⟩
    exact ((mem_subType M phi).mp this).2
  · intro hv
    have : psi ∈ subType M phi w := h.symm ▸ (mem_subType M phi).mpr ⟨hpsi, hv⟩
    exact ((mem_subType M phi).mp this).2

/-- `R` is a filtration of `M` through `sub φ`: it relates the types of related worlds (`min`),
and `□ψ ∈ sub φ` at `w` forces `ψ` at every world whose type is related to that of `w` (`max`).
These are conditions (ii) and (iii) of Blackburn–de Rijke–Venema, Definition 2.36, in `□` form;
conditions (i) and (iv) (worlds are the `Σ`-types, atoms of `Σ` true where they belong) are built
into `filtrationWorlds` and `finModel`. -/
structure IsFiltration (R : Finset (Finset (Formula Atom) × Finset (Formula Atom))) : Prop where
  min : ∀ {w v}, M.rel w v → (subType M phi w, subType M phi v) ∈ R
  max : ∀ {w v}, (subType M phi w, subType M phi v) ∈ R → ∀ {psi}, Formula.box psi ∈ phi.sub →
    M.Satisfies w (.box psi) → M.Satisfies v psi

/-- **Filtration lemma** for any filtration `R`: at the type of `w`, the finite model agrees with
`M` at `w` on every formula of `sub φ`. -/
theorem satisfies_finModel_filtrationWorlds_iff
    {R : Finset (Finset (Formula Atom) × Finset (Formula Atom))} (hR : IsFiltration M phi R)
    {psi : Formula Atom} (hpsi : psi ∈ phi.sub) (w : World) :
    (finModel (filtrationWorlds M phi) R (filtrationWorlds_nonempty M phi)).Satisfies
      ⟨subType M phi w, subType_mem_filtrationWorlds M phi w⟩ psi ↔ M.Satisfies w psi := by
  induction psi generalizing w with
  | atom p =>
    change Formula.atom p ∈ subType M phi w ↔ _
    rw [mem_subType]
    exact and_iff_right hpsi
  | bot => exact Iff.rfl
  | imp a b iha ihb =>
    rw [KripkeModel.satisfies_imp, KripkeModel.satisfies_imp,
      iha (Formula.mem_sub_of_imp_mem_left hpsi), ihb (Formula.mem_sub_of_imp_mem_right hpsi)]
  | box a iha =>
    have ha := Formula.mem_sub_of_box_mem hpsi
    rw [KripkeModel.satisfies_box, KripkeModel.satisfies_box]
    constructor
    · intro h w' hww'
      exact (iha ha w').mp (h ⟨_, subType_mem_filtrationWorlds M phi w'⟩ (hR.min hww'))
    · intro h t hrel
      obtain ⟨v, hv⟩ := exists_subType_eq M phi t.2
      have ht : t = ⟨subType M phi v, subType_mem_filtrationWorlds M phi v⟩ := Subtype.ext hv.symm
      subst ht
      exact (iha ha v).mpr (hR.max hrel hpsi h)

/-- The smallest filtration is a filtration. -/
theorem isFiltration_filtrationRel : IsFiltration M phi (filtrationRel M phi) where
  min hwv := (mem_filtrationRel M phi).mpr ⟨_, _, rfl, rfl, hwv⟩
  max {w v} hrel psi hpsi hbox := by
    obtain ⟨w', v', hw', hv', hw'v'⟩ := (mem_filtrationRel M phi).mp hrel
    have hbox' := (satisfies_iff_of_subType_eq M phi hw' hpsi).mpr hbox
    exact (satisfies_iff_of_subType_eq M phi hv' (Formula.mem_sub_of_box_mem hpsi)).mp
      (hbox' v' hw'v')

/-- The filtration of `M` through the subformulas of `φ`. -/
noncomputable def filtration : KripkeModel {s // s ∈ filtrationWorlds M phi} Atom :=
  finModel (filtrationWorlds M phi) (filtrationRel M phi) (filtrationWorlds_nonempty M phi)

/-- **Filtration lemma** for the smallest filtration: a subformula of `φ` holds at the type of `w`
iff it holds at `w`. -/
theorem satisfies_filtration_iff {psi : Formula Atom} (hpsi : psi ∈ phi.sub) (w : World) :
    (filtration M phi).Satisfies ⟨subType M phi w, subType_mem_filtrationWorlds M phi w⟩ psi ↔
      M.Satisfies w psi :=
  satisfies_finModel_filtrationWorlds_iff M phi (isFiltration_filtrationRel M phi) hpsi w

theorem card_filtrationWorlds_le :
    (filtrationWorlds M phi).card ≤ 2 ^ phi.sub.card := by
  classical
  calc (filtrationWorlds M phi).card ≤ phi.sub.powerset.card := Finset.card_filter_le _ _
    _ = 2 ^ phi.sub.card := Finset.card_powerset _

end Filtration

/-! ### Finite model property and decidability -/

omit [DecidableEq Atom] in
/-- A formula that is not a K-theorem fails at some world of some Kripke model. -/
theorem exists_not_satisfies_of_not_derivable_K {phi : Formula Atom}
    (h : ¬Derivable Axioms.K phi) :
    ∃ (W : Type u) (M : KripkeModel W Atom) (w : W), ¬M.Satisfies w phi := by
  by_contra hall
  push Not at hall
  exact h (derivable_K_iff.mpr fun W M w ↦ hall W M w)

/-- **Finite model property of K**: a formula that is not a K-theorem fails in a Kripke model with
at most `2 ^ |sub φ|` worlds. -/
theorem exists_finite_countermodel {phi : Formula Atom} (h : ¬Derivable Axioms.K phi) :
    ∃ (W : Type u) (_ : Fintype W) (M : KripkeModel W Atom),
      Fintype.card W ≤ 2 ^ phi.sub.card ∧ ¬M.Valid phi := by
  obtain ⟨W, M, w, hw⟩ := exists_not_satisfies_of_not_derivable_K h
  refine ⟨_, inferInstance, filtration M phi, ?_, fun hval ↦ hw ?_⟩
  · rw [Fintype.card_coe]
    exact card_filtrationWorlds_le M phi
  · exact (satisfies_filtration_iff M phi (Formula.mem_sub_self phi) w).mp (hval _)

/-- The finite check behind decidability: `φ` holds in every model on a nonempty set `U` of subsets
of `sub φ`, for every relation `R ⊆ U × U`. -/
def FinValid (phi : Formula Atom) : Prop :=
  ∀ U ∈ phi.sub.powerset.powerset, U.Nonempty → ∀ R ∈ (U ×ˢ U).powerset, ∀ s ∈ U,
    evalFin U R s phi = true

instance (phi : Formula Atom) : Decidable (FinValid phi) := by
  unfold FinValid
  infer_instance

/-- `φ` is a K-theorem iff it passes the finite check. -/
theorem derivable_K_iff_finValid {phi : Formula Atom} :
    Derivable Axioms.K phi ↔ FinValid phi := by
  constructor
  · intro h U _ hU R _ s hs
    exact (satisfies_finModel_iff U R hU ⟨s, hs⟩ phi).mp (h.valid_K _)
  · intro h
    by_contra hd
    obtain ⟨W, M, w, hw⟩ := exists_not_satisfies_of_not_derivable_K hd
    have hU : filtrationWorlds M phi ∈ phi.sub.powerset.powerset := by
      classical
      simp only [Finset.mem_powerset]
      exact Finset.filter_subset _ _
    have hR : filtrationRel M phi ∈
        (filtrationWorlds M phi ×ˢ filtrationWorlds M phi).powerset := by
      classical
      simp only [Finset.mem_powerset]
      exact Finset.filter_subset _ _
    have heval := h _ hU (filtrationWorlds_nonempty M phi) _ hR _
      (subType_mem_filtrationWorlds M phi w)
    refine hw ((satisfies_filtration_iff M phi (Formula.mem_sub_self phi) w).mp ?_)
    exact (satisfies_finModel_iff _ _ (filtrationWorlds_nonempty M phi) _ phi).mpr heval

/-- `φ` is a K-theorem iff it holds in every model `finModel U R` on subsets of `sub φ`. -/
theorem derivable_K_iff_forall_finModel {phi : Formula Atom} :
    Derivable Axioms.K phi ↔
      ∀ U ⊆ phi.sub.powerset, ∀ (hU : U.Nonempty) (R : Finset (Finset (Formula Atom) ×
        Finset (Formula Atom))), (finModel U R hU).Valid phi := by
  refine ⟨fun h _ _ _ _ ↦ h.valid_K, fun h ↦ derivable_K_iff_finValid.mpr ?_⟩
  intro U hU hUne R _ s hs
  exact (satisfies_finModel_iff U R hUne ⟨s, hs⟩ phi).mp
    (h U (Finset.mem_powerset.mp hU) hUne R ⟨s, hs⟩)

/-- **Decidability of K**: provability in K is decidable. -/
instance instDecidablePredDerivableK : DecidablePred (Derivable (Axioms.K : Set (Formula Atom))) :=
  fun _ ↦ decidable_of_iff _ derivable_K_iff_finValid.symm

end Modal
end Cslib
