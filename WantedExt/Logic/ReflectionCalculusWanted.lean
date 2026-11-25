/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.Modal.ReflectionCalculusCompleteness
public import Mathlib.SetTheory.Ordinal.Veblen

/-!
# Ordinal assignment for worms in the Reflection Calculus

The wanted ordinal assignment uses the sequent calculus and worms from
`CSLibExt.Logics.Modal.ReflectionCalculus`.
-/

@[expose] public section

namespace Cslib
namespace Modal
namespace RC

/-- **Worms have order type `ε₀`.** There is a map `o` from worms to ordinals such that two worms
are RC-equivalent iff they have the same value, `α <₀ β` iff `o α < o β`, and the values are
exactly the ordinals below `ε₀`; that is, worms modulo RC-equivalence, ordered by `<₀`, are
order-isomorphic to `ε₀`. Beklemishev states this for GLP, with `α <₀ β` iff
`GLP ⊢ β → ⟨0⟩α`, together with the fact that every closed strictly positive formula is
GLP-equivalent to a worm ("Provability algebras: an overview and current progress", slides, 2012,
on the positive closed fragment as an ordinal notation system); the result is due to
Beklemishev, "Provability algebras and proof-theoretic ordinals, I", *Annals of Pure and Applied
Logic* 128 (2004), listed in Verbrugge, "Provability logic", *Stanford Encyclopedia of
Philosophy*, §5.4 under "GLP and proof-theoretic ordinals" (that paper was not read here).
The RC form stated here
follows because RC axiomatizes the strictly positive fragment of GLP (Dashkov, as reported in
arXiv:1304.4396v3, Section 2). The proved
`WormLt.replicate_zero_one` is the instance `o(0^k) = k < ω = o(1)`. -/
theorem_wanted exists_wormOrdinal :
    ∃ o : List ℕ → Ordinal.{0},
      (∀ α β, o α = o β ↔
        (Derives (worm α : Formula Empty) (worm β) ∧
          Derives (worm β : Formula Empty) (worm α))) ∧
      (∀ α β, WormLt (Atom := Empty) α β ↔ o α < o β) ∧
      Set.range o = Set.Iio (Ordinal.epsilon 0)

end RC
end Modal
end Cslib
