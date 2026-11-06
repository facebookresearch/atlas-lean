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

/-- **Subformulas.** The finite set $\mathrm{sub}(\varphi)$ of subformulas of a modal formula
$\varphi$, including $\varphi$ itself, is defined by recursion: $\mathrm{sub}(p) = \{p\}$ for an
atom $p$, $\mathrm{sub}(\bot) = \{\bot\}$, $\mathrm{sub}(\varphi \to \psi) = \{\varphi \to \psi\}
\cup \mathrm{sub}(\varphi) \cup \mathrm{sub}(\psi)$, and $\mathrm{sub}(\Box\varphi) =
\{\Box\varphi\} \cup \mathrm{sub}(\varphi)$. -/
def sub : Formula Atom → Finset (Formula Atom)
  | .atom p => {.atom p}
  | .bot => {.bot}
  | .imp phi psi => insert (.imp phi psi) (sub phi ∪ sub psi)
  | .box phi => insert (.box phi) (sub phi)

theorem mem_sub_self (phi : Formula Atom) : phi ∈ phi.sub := by
  cases phi <;> simp [sub]

/-- **The subformula relation is transitive.** If $\psi$ is a subformula of a modal formula
$\varphi$, then every subformula of $\psi$ is a subformula of $\varphi$. -/
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

/-- **Finite Kripke model on sets of formulas.** Let $U$ be a nonempty finite set of finite sets of
formulas and $R$ a finite set of pairs of finite sets of formulas. The Kripke model on $U$ with
relation $R$ has the elements of $U$ as worlds, a world $s$ sees a world $t$ iff $(s, t) \in R$,
and an atom $p$ is true at $s$ iff $p \in s$. -/
def finModel (U : Finset (Finset (Formula Atom))) (R : Finset (Finset (Formula Atom) ×
    Finset (Formula Atom))) (hU : U.Nonempty) : KripkeModel {s // s ∈ U} Atom where
  nonempty_world := let ⟨s, hs⟩ := hU; ⟨⟨s, hs⟩⟩
  rel s t := (s.1, t.1) ∈ R
  valuation s p := Formula.atom p ∈ s.1

/-- **Boolean evaluation in a finite model.** Given a finite set $U$ of finite sets of formulas, a
finite set $R$ of pairs of such sets and a finite set $s$ of formulas, the Boolean value of a
formula at $s$ is defined by recursion on the formula: an atom $p$ is true iff $p \in s$; $\bot$ is
false; $\varphi \to \psi$ is true iff $\varphi$ is false or $\psi$ is true at $s$; and $\Box\varphi$
is true iff $\varphi$ is true at every $t \in U$ with $(s, t) \in R$.

For $s \in U$ this computes satisfaction at $s$ in the finite Kripke model on $U$ with relation
$R$ in which an atom is true at a world iff it belongs to it. -/
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

/-- **Type of a world.** Given a Kripke model $M$ and a modal formula $\varphi$, the type (or
$\Sigma$-type, for $\Sigma$ the set of subformulas of $\varphi$) of a world $w$ of $M$ is the
finite set of subformulas of $\varphi$ that hold at $w$ in $M$. -/
noncomputable def subType (w : World) : Finset (Formula Atom) := by
  classical exact phi.sub.filter fun psi ↦ M.Satisfies w psi

theorem mem_subType {w : World} {psi : Formula Atom} :
    psi ∈ subType M phi w ↔ psi ∈ phi.sub ∧ M.Satisfies w psi := by
  classical
  simp [subType]

/-- **Worlds of the filtration.** Let $M$ be a Kripke model and $\varphi$ a modal formula. The
worlds of the filtration of $M$ through the subformulas of $\varphi$ form the finite set of types
occurring in $M$: the subsets $s$ of the set $\mathrm{sub}(\varphi)$ of subformulas of $\varphi$
such that $s$ is the set of subformulas of $\varphi$ satisfied at some world of $M$. -/
noncomputable def filtrationWorlds : Finset (Finset (Formula Atom)) := by
  classical exact phi.sub.powerset.filter fun s ↦ ∃ w, subType M phi w = s

/-- **Smallest filtration relation.** Let $M$ be a Kripke model and $\varphi$ a modal formula, and
call the set of subformulas of $\varphi$ satisfied at a world $w$ of $M$ the type of $w$. The
smallest filtration relation is the finite set of pairs $(s, t)$ of types such that there are
worlds $w$ and $w'$ of $M$ of types $s$ and $t$ with $w'$ accessible from $w$. -/
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

/-- **Filtration worlds are realized types.** Let $M$ be a Kripke model and $\varphi$ a modal
formula, and call the set of subformulas of $\varphi$ satisfied at a world $w$ of $M$ the type of
$w$. Every world $s$ of the filtration of $M$ through the subformulas of $\varphi$, that is, every
element of the finite set of types occurring in $M$, is the type of some world of $M$. -/
theorem exists_subType_eq {s : Finset (Formula Atom)} (hs : s ∈ filtrationWorlds M phi) :
    ∃ w, subType M phi w = s := by
  classical
  simp only [filtrationWorlds, Finset.mem_filter] at hs
  exact hs.2

/-- **Worlds of the same type agree on subformulas.** Let $M$ be a Kripke model and $\varphi$ a
modal formula, and call the set of subformulas of $\varphi$ true at a world $w$ of $M$ the type
of $w$. If two worlds $w$ and $v$ of $M$ have the same type, then every subformula $\psi$ of
$\varphi$ holds at $w$ iff it holds at $v$. -/
theorem satisfies_iff_of_subType_eq {w v : World} (h : subType M phi w = subType M phi v)
    {psi : Formula Atom} (hpsi : psi ∈ phi.sub) : M.Satisfies w psi ↔ M.Satisfies v psi := by
  constructor
  · intro hw
    have : psi ∈ subType M phi v := h ▸ (mem_subType M phi).mpr ⟨hpsi, hw⟩
    exact ((mem_subType M phi).mp this).2
  · intro hv
    have : psi ∈ subType M phi w := h.symm ▸ (mem_subType M phi).mpr ⟨hpsi, hv⟩
    exact ((mem_subType M phi).mp this).2

/-- **Filtration relations.** Let $M$ be a Kripke model, $\varphi$ a modal formula, $\Sigma$ the
set of subformulas of $\varphi$, and for a world $w$ let $[w]$, the type of $w$, be the set of
formulas of $\Sigma$ true at $w$ in $M$. A relation $R$ on finite sets of formulas is a
filtration of $M$ through $\Sigma$ when (min) for all worlds $w, v$ related in $M$, the pair
$([w], [v])$ is in $R$, and (max) for all worlds $w, v$ with $([w], [v]) \in R$ and every
formula $\psi$ with $\Box\psi \in \Sigma$, if $\Box\psi$ holds at $w$ in $M$ then $\psi$ holds at
$v$ in $M$.

These are conditions (ii) and (iii) of Blackburn–de Rijke–Venema, Definition 2.36, in $\Box$
form; conditions (i) and (iv) (worlds are the $\Sigma$-types, atoms of $\Sigma$ true where they
belong) are built into the construction of the finite model. -/
structure IsFiltration (R : Finset (Finset (Formula Atom) × Finset (Formula Atom))) : Prop where
  min : ∀ {w v}, M.rel w v → (subType M phi w, subType M phi v) ∈ R
  max : ∀ {w v}, (subType M phi w, subType M phi v) ∈ R → ∀ {psi}, Formula.box psi ∈ phi.sub →
    M.Satisfies w (.box psi) → M.Satisfies v psi

/-- **Filtration lemma.** Let $M$ be a Kripke model, $\varphi$ a modal formula, and for a world
$w$ let $[w]$, the type of $w$, be the set of subformulas of $\varphi$ true at $w$ in $M$. Let $R$
be a filtration of $M$ through the subformulas of $\varphi$, and let $M^R$ be the Kripke model
whose worlds are the types of the worlds of $M$, with accessibility relation $R$ and an atom
true at a type iff the type contains it. Then for every subformula $\psi$ of $\varphi$ and every
world $w$ of $M$, $\psi$ holds at $[w]$ in $M^R$ iff $\psi$ holds at $w$ in $M$. -/
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

/-- **The smallest filtration is a filtration.** Let $M$ be a Kripke model and $\varphi$ a modal
formula, and call the set of subformulas of $\varphi$ true at a world $w$ the type of $w$. The
relation that relates two types when some worlds of those types are related in $M$ is a
filtration of $M$ through the set of subformulas of $\varphi$. -/
theorem isFiltration_filtrationRel : IsFiltration M phi (filtrationRel M phi) where
  min hwv := (mem_filtrationRel M phi).mpr ⟨_, _, rfl, rfl, hwv⟩
  max {w v} hrel psi hpsi hbox := by
    obtain ⟨w', v', hw', hv', hw'v'⟩ := (mem_filtrationRel M phi).mp hrel
    have hbox' := (satisfies_iff_of_subType_eq M phi hw' hpsi).mpr hbox
    exact (satisfies_iff_of_subType_eq M phi hv' (Formula.mem_sub_of_box_mem hpsi)).mp
      (hbox' v' hw'v')

/-- **Smallest filtration of a Kripke model.** Let $M$ be a Kripke model and $\varphi$ a modal
formula, and call the set of subformulas of $\varphi$ satisfied at a world $w$ of $M$ the type of
$w$. The filtration of $M$ through the subformulas of $\varphi$ is the Kripke model whose worlds
are the types occurring in $M$, in which a type $s$ sees a type $t$ iff some world of type $s$
sees some world of type $t$ in $M$, and in which an atom $p$ is true at $s$ iff $p \in s$. -/
noncomputable def filtration : KripkeModel {s // s ∈ filtrationWorlds M phi} Atom :=
  finModel (filtrationWorlds M phi) (filtrationRel M phi) (filtrationWorlds_nonempty M phi)

/-- **Filtration lemma for the smallest filtration.** Let $M$ be a Kripke model, $\varphi$ a
modal formula, and for a world $w$ let $[w]$, the type of $w$, be the set of subformulas of
$\varphi$ true at $w$ in $M$. For every subformula $\psi$ of $\varphi$ and every world $w$ of $M$,
$\psi$ holds at $[w]$ in the smallest filtration of $M$ through the subformulas of $\varphi$ iff
$\psi$ holds at $w$ in $M$. -/
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
/-- **Completeness of K, countermodel form.** A modal formula that is not a theorem of K fails at
some world of some Kripke model. -/
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

/-- **Finite validity check for K.** A modal formula $\varphi$ passes the finite check when,
for every nonempty set $U$ of subsets of the set $\mathrm{sub}(\varphi)$ of subformulas of
$\varphi$, every relation $R \subseteq U \times U$ and every $s \in U$, the formula $\varphi$
is true at $s$ in the Kripke model with set of worlds $U$, accessibility relation $R$, and an
atom $p$ true at a world $t$ iff $p \in t$; truth is computed by recursion on $\varphi$. -/
def FinValid (phi : Formula Atom) : Prop :=
  ∀ U ∈ phi.sub.powerset.powerset, U.Nonempty → ∀ R ∈ (U ×ˢ U).powerset, ∀ s ∈ U,
    evalFin U R s phi = true

instance (phi : Formula Atom) : Decidable (FinValid phi) := by
  unfold FinValid
  infer_instance

/-- **Finite-check criterion for K-theorems.** A modal formula $\varphi$ is a theorem of K iff it
passes the following finite check: for every nonempty set $U$ of subsets of the set
$\mathrm{sub}(\varphi)$ of subformulas of $\varphi$, every relation $R \subseteq U \times U$ and
every $s \in U$, $\varphi$ evaluates to true at $s$ in the finite Kripke model on $U$ with
relation $R$ in which an atom $p$ is true at $s$ iff $p \in s$. -/
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

/-- **K-theorems via finite models on sets of subformulas.** A modal formula $\varphi$ is a theorem
of K iff for every nonempty set $U$ of subsets of the set $\mathrm{sub}(\varphi)$ of subformulas of
$\varphi$ and every finite set $R$ of pairs of finite sets of formulas, $\varphi$ holds at every
world of the Kripke model whose worlds are the elements of $U$, in which $s$ sees $t$ iff
$(s, t) \in R$, and in which an atom $p$ is true at $s$ iff $p \in s$. -/
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
