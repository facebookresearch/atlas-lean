/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Set.Function
public import Mathlib.Order.Monotone.Defs

/-!
# Security levels, policies and low equivalence

In the lattice model of information flow, security levels are ordered by `≤` (written `⊑`,
read "may flow to"), a security policy `Γ : V → L` gives each program variable a level, and a
store `σ : V → α` gives each variable a value. An observer at level `ℓ` sees the variables of
level at most `ℓ`, so two stores are *low equivalent* at `ℓ`, written `σ₁ =_ℓ σ₂`, when they
agree on all of them (`LowEquiv`).

The definition needs only the relation `≤` on levels. Low equivalence is an equivalence relation
whatever that relation is (`lowEquiv_equivalence`); for a preorder it is antitone in the
observer level (`antitone_lowEquiv`). For values with at least two elements, low equivalence at
`ℓ` determines the value of a variable `x` exactly when `Γ x ≤ ℓ` (`forall_lowEquiv_eq_iff_le`).
Two consequences explain the lattice operations of the model:

* joins give the level of combined information: low equivalence at `ℓ` determines the values of
  all variables of a finite set `s` exactly when `s.sup Γ ≤ ℓ`
  (`forall_lowEquiv_eqOn_iff_sup_le`);
* the permitted flows are those that preserve low equivalence: copying `x` into `y` maps
  low-equivalent stores to low-equivalent stores at every observer level exactly when
  `Γ x ≤ Γ y` (`forall_lowEquiv_update_iff_le`).

The two-point lattice `L ⊑ H` is Mathlib's `Bool`, with `false ≤ true`. At its bottom, low
equivalence is agreement on the variables of the least level (`lowEquiv_bot_iff`), the relation
`=_L` of Sabelfeld and Myers; at its top it is equality (`lowEquiv_top_iff`).

## References

* D. Volpano, C. Irvine and G. Smith, "A sound type system for secure flow analysis",
  *Journal of Computer Security* 4(2–3):167–187, 1996: Section 2 (the lattice model, permitted
  flows and least upper bounds) and Theorem 6.8 (agreement on all locations of level at most
  `τ`).
* A. Sabelfeld and A. C. Myers, "Language-based information-flow security", *IEEE Journal on
  Selected Areas in Communications* 21(1):5–19, 2003: Section II-G (public and confidential
  data) and Section III-A (the relation `=_L`).
-/

@[expose] public section

namespace Cslib.Security.InformationFlow

open Set

variable {V L α : Type*}

section LE

variable [LE L]

/-- **Low equivalence.** Let security levels carry a relation $\sqsubseteq$, let a security
policy $\Gamma : V \to \mathcal{L}$ assign a level to each variable, and let stores
$\sigma_1, \sigma_2 : V \to A$ assign a value to each variable. For an observer at level $\ell$,
the stores are low equivalent, $\sigma_1 =_\ell \sigma_2$, when $\sigma_1(x) = \sigma_2(x)$ for
every variable $x$ with $\Gamma(x) \sqsubseteq \ell$. -/
def LowEquiv (Γ : V → L) (ℓ : L) (σ₁ σ₂ : V → α) : Prop :=
  EqOn σ₁ σ₂ {x | Γ x ≤ ℓ}

variable {Γ : V → L} {ℓ : L} {σ₁ σ₂ σ₃ : V → α}

theorem lowEquiv_iff : LowEquiv Γ ℓ σ₁ σ₂ ↔ ∀ x, Γ x ≤ ℓ → σ₁ x = σ₂ x :=
  Iff.rfl

namespace LowEquiv

@[refl]
protected theorem refl (Γ : V → L) (ℓ : L) (σ : V → α) : LowEquiv Γ ℓ σ σ :=
  eqOn_refl σ _

@[symm]
protected theorem symm (h : LowEquiv Γ ℓ σ₁ σ₂) : LowEquiv Γ ℓ σ₂ σ₁ :=
  EqOn.symm h

@[trans]
protected theorem trans (h₁ : LowEquiv Γ ℓ σ₁ σ₂) (h₂ : LowEquiv Γ ℓ σ₂ σ₃) :
    LowEquiv Γ ℓ σ₁ σ₃ :=
  EqOn.trans h₁ h₂

theorem update [DecidableEq V] (h : LowEquiv Γ ℓ σ₁ σ₂) {y : V} {v₁ v₂ : α}
    (hv : Γ y ≤ ℓ → v₁ = v₂) :
    LowEquiv Γ ℓ (Function.update σ₁ y v₁) (Function.update σ₂ y v₂) := by
  intro x hx
  rcases eq_or_ne x y with rfl | hxy
  · simpa using hv hx
  · simpa [Function.update_of_ne hxy] using h hx

end LowEquiv

/-- **Low equivalence is an equivalence relation.** Let security levels carry any relation
$\sqsubseteq$ and let $\Gamma : V \to \mathcal{L}$ be a security policy. For every observer level
$\ell$, low equivalence $=_\ell$ (agreement on every variable $x$ with
$\Gamma(x) \sqsubseteq \ell$) is reflexive, symmetric and transitive on stores
$V \to A$. -/
theorem lowEquiv_equivalence (Γ : V → L) (ℓ : L) : Equivalence (LowEquiv (α := α) Γ ℓ) :=
  ⟨LowEquiv.refl Γ ℓ, LowEquiv.symm, LowEquiv.trans⟩

theorem forall_lowEquiv_eq_iff_le [Nontrivial α] {x : V} :
    (∀ σ₁ σ₂ : V → α, LowEquiv Γ ℓ σ₁ σ₂ → σ₁ x = σ₂ x) ↔ Γ x ≤ ℓ := by
  classical
  refine ⟨fun h => ?_, fun hx σ₁ σ₂ hσ => hσ hx⟩
  by_contra hx
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  refine hab ?_
  have key := h (fun _ => a) (Function.update (fun _ => a) x b) fun z hz => ?_
  · simpa using key
  · have hzx : z ≠ x := by
      rintro rfl
      exact hx hz
    simp [Function.update_of_ne hzx]

theorem forall_lowEquiv_update_iff [DecidableEq V] [Nontrivial α] {x y : V} :
    (∀ σ₁ σ₂ : V → α, LowEquiv Γ ℓ σ₁ σ₂ →
        LowEquiv Γ ℓ (Function.update σ₁ y (σ₁ x)) (Function.update σ₂ y (σ₂ x))) ↔
      (Γ y ≤ ℓ → Γ x ≤ ℓ) := by
  refine ⟨fun h hy => (forall_lowEquiv_eq_iff_le (α := α)).1 fun σ₁ σ₂ hσ => ?_,
    fun h σ₁ σ₂ hσ => hσ.update fun hy => hσ (h hy)⟩
  simpa using h σ₁ σ₂ hσ hy

theorem lowEquiv_top_iff [OrderTop L] : LowEquiv Γ ⊤ σ₁ σ₂ ↔ σ₁ = σ₂ := by
  simp [LowEquiv, ← eqOn_univ]

end LE

section Preorder

variable [Preorder L] {Γ : V → L}

theorem LowEquiv.mono {ℓ ℓ' : L} {σ₁ σ₂ : V → α} (hℓ : ℓ ≤ ℓ') (h : LowEquiv Γ ℓ' σ₁ σ₂) :
    LowEquiv Γ ℓ σ₁ σ₂ :=
  EqOn.mono (fun _ hx => le_trans hx hℓ) h

/-- **Low equivalence is antitone in the observer level.** Let security levels be preordered
by $\sqsubseteq$ and let $\Gamma : V \to \mathcal{L}$ be a security policy. If
$\ell \sqsubseteq \ell'$, then stores $\sigma_1, \sigma_2 : V \to A$ with
$\sigma_1 =_{\ell'} \sigma_2$ satisfy $\sigma_1 =_\ell \sigma_2$: an observer at a higher level
distinguishes at least the stores that one at a lower level distinguishes. -/
theorem antitone_lowEquiv (Γ : V → L) : Antitone (LowEquiv (α := α) Γ) :=
  fun _ _ hℓ _ _ h => h.mono hℓ

/-- **Copying $x$ into $y$ keeps low equivalence exactly when $\Gamma(x) \sqsubseteq \Gamma(y)$.**
Let security levels be preordered by $\sqsubseteq$, let $\Gamma : V \to \mathcal{L}$ be a
security policy, let $x, y \in V$, and let the set $A$ of values have at least two elements.
Copying $x$ into $y$, which maps a store $\sigma$ to $\sigma[y \mapsto \sigma(x)]$, maps stores
with $\sigma_1 =_\ell \sigma_2$ to stores with
$\sigma_1[y \mapsto \sigma_1(x)] =_\ell \sigma_2[y \mapsto \sigma_2(x)]$ for every observer level
$\ell$ if and only if $\Gamma(x) \sqsubseteq \Gamma(y)$. -/
theorem forall_lowEquiv_update_iff_le [DecidableEq V] [Nontrivial α] {x y : V} :
    (∀ (ℓ : L) (σ₁ σ₂ : V → α), LowEquiv Γ ℓ σ₁ σ₂ →
        LowEquiv Γ ℓ (Function.update σ₁ y (σ₁ x)) (Function.update σ₂ y (σ₂ x))) ↔
      Γ x ≤ Γ y := by
  simp only [forall_lowEquiv_update_iff]
  exact forall_ge_iff_le

end Preorder

theorem lowEquiv_bot_iff [PartialOrder L] [OrderBot L] {Γ : V → L} {σ₁ σ₂ : V → α} :
    LowEquiv Γ ⊥ σ₁ σ₂ ↔ ∀ x, Γ x = ⊥ → σ₁ x = σ₂ x := by
  simp [lowEquiv_iff]

/-- **Joins give the level of combined information.** Let security levels form a
join-semilattice $(\mathcal{L}, \sqsubseteq)$ with a least element, let
$\Gamma : V \to \mathcal{L}$ be a security policy, let $S \subseteq V$ be a finite set of
variables, and let the set $A$ of values have at least two elements. For an observer at level
$\ell$, every two stores $\sigma_1, \sigma_2 : V \to A$ with $\sigma_1 =_\ell \sigma_2$ agree on
every variable of $S$ if and only if $\bigsqcup_{x \in S} \Gamma(x) \sqsubseteq \ell$. -/
theorem forall_lowEquiv_eqOn_iff_sup_le [SemilatticeSup L] [OrderBot L] [Nontrivial α]
    {Γ : V → L} {ℓ : L} {s : Finset V} :
    (∀ σ₁ σ₂ : V → α, LowEquiv Γ ℓ σ₁ σ₂ → EqOn σ₁ σ₂ s) ↔ s.sup Γ ≤ ℓ := by
  rw [Finset.sup_le_iff]
  exact ⟨fun h x hx => (forall_lowEquiv_eq_iff_le (α := α)).1 fun σ₁ σ₂ hσ => h σ₁ σ₂ hσ hx,
    fun h σ₁ σ₂ hσ x hx => hσ (h x hx)⟩

end Cslib.Security.InformationFlow
