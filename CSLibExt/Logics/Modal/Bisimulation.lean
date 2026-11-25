/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bisimulations between Kripke models
-/
module

public import CSLibExt.Logics.Modal.Kripke

/-!
# Bisimulations between Kripke models

A bisimulation is a relation between the worlds of two Kripke models that
matches atoms and matches accessible worlds in both directions (the forth and
back conditions). Bisimilar worlds satisfy exactly the same modal formulas
(`Bisimulation.satisfies_iff`), so bisimilarity is the semantic equivalence
relation of basic modal logic. This is the invariance half of the van Benthem
characterization theorem: every modal formula, viewed through the standard
translation, is invariant under bisimulations.

## References

- P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, Cambridge University Press, 2001,
  §2.2 (bisimulations and modal equivalence), §2.7 (van Benthem characterization).
- J. van Benthem, *Modal Correspondence Theory*, PhD thesis, University of Amsterdam, 1976;
  *Modal Logic and Classical Logic*, Bibliopolis, 1983.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Cslib.Modal

variable {Atom : Type u} {W : Type v} {V : Type w}

/-- **Bisimulation.** Let $M$ and $N$ be Kripke models over the same atoms, with sets of
worlds $W$ and $V$ and accessibility relations $R_M$ and $R_N$. A relation
$Z \subseteq W \times V$ is a bisimulation between $M$ and $N$ when, for all $w \in W$ and
$v \in V$ with $w \mathrel{Z} v$: each atom $a$ is true at $w$ in $M$ if and only if $a$ is
true at $v$ in $N$; for every $w'$ with $w \mathrel{R_M} w'$ there is $v'$ with
$v \mathrel{R_N} v'$ and $w' \mathrel{Z} v'$ (forth); and for every $v'$ with
$v \mathrel{R_N} v'$ there is $w'$ with $w \mathrel{R_M} w'$ and $w' \mathrel{Z} v'$ (back). -/
structure Bisimulation (M : KripkeModel W Atom) (N : KripkeModel V Atom)
    (R : W → V → Prop) : Prop where
  /-- Related worlds agree on every atom. -/
  atom_iff : ∀ {w v}, R w v → ∀ a, M.valuation w a ↔ N.valuation v a
  /-- Every accessible world of the first model is matched by an accessible world of the
    second. -/
  forth : ∀ {w v w'}, R w v → M.rel w w' → ∃ v', N.rel v v' ∧ R w' v'
  /-- Every accessible world of the second model is matched by an accessible world of the
    first. -/
  back : ∀ {w v v'}, R w v → N.rel v v' → ∃ w', M.rel w w' ∧ R w' v'

namespace Bisimulation

variable {M : KripkeModel W Atom} {N : KripkeModel V Atom} {R : W → V → Prop}

/-- **Bisimulations preserve modal formulas.** Let $Z$ be a bisimulation between Kripke models
$M$ and $N$ over the same atoms. If $Z$ relates a world $w$ of $M$ to a world $v$ of $N$, then
every modal formula $\varphi$ is satisfied at $w$ in $M$ if and only if $\varphi$ is satisfied
at $v$ in $N$. -/
theorem satisfies_iff (h : Bisimulation M N R) (φ : Formula Atom) (w : W) (v : V)
    (hr : R w v) : M.Satisfies w φ ↔ N.Satisfies v φ := by
  induction φ generalizing w v with
  | atom a => exact h.atom_iff hr a
  | bot => rfl
  | imp φ ψ ihφ ihψ =>
    simp only [KripkeModel.Satisfies]
    constructor
    · intro hφ hψ
      exact (ihψ w v hr).mp (hφ ((ihφ w v hr).mpr hψ))
    · intro hφ hψ
      exact (ihψ w v hr).mpr (hφ ((ihφ w v hr).mp hψ))
  | box φ ih =>
    constructor
    · intro hbox v' hrel
      obtain ⟨w', hw', hr'⟩ := h.back hr hrel
      exact (ih w' v' hr').mp (hbox w' hw')
    · intro hbox w' hrel
      obtain ⟨v', hv', hr'⟩ := h.forth hr hrel
      exact (ih w' v' hr').mpr (hbox v' hv')

/-- **Bisimilar worlds.** Let $M$ and $N$ be Kripke models over the same atoms. A world $w$ of
$M$ and a world $v$ of $N$ are bisimilar if some bisimulation between $M$ and $N$ relates $w$
to $v$. -/
def Bisimilar (M : KripkeModel W Atom) (N : KripkeModel V Atom) (w : W) (v : V) : Prop :=
  ∃ R : W → V → Prop, Bisimulation M N R ∧ R w v

/-- **Bisimilar worlds are modally equivalent.** If a world $w$ of a Kripke model $M$ and a world
$v$ of a Kripke model $N$ over the same atoms are bisimilar, then every modal formula $\varphi$
is satisfied at $w$ in $M$ if and only if $\varphi$ is satisfied at $v$ in $N$. -/
theorem Bisimilar.satisfies_iff {M : KripkeModel W Atom} {N : KripkeModel V Atom}
    {w : W} {v : V} (h : Bisimilar M N w v) (φ : Formula Atom) :
    M.Satisfies w φ ↔ N.Satisfies v φ := by
  obtain ⟨R, hR, hr⟩ := h
  exact hR.satisfies_iff φ w v hr

end Bisimulation

end Cslib.Modal
