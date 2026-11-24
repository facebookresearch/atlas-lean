/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.Modal.ReflectionCalculus
public import Mathlib.SetTheory.Ordinal.Veblen

/-!
# Reflection Calculus: wanted results

Established results about Beklemishev's Reflection Calculus RC (modalities in `ℕ`), over the
sequent calculus `Cslib.Modal.RC.Derives` of `CSLibExt.Logics.Modal.ReflectionCalculus`, recorded
without proof.

* `derives_iff_forall_frame`: Kripke completeness of RC.
* `exists_wormOrdinal`: worms ordered by `<₀` have order type `ε₀`.
-/

@[expose] public section

namespace Cslib
namespace Modal
namespace RC

universe u

/-- **Kripke completeness of RC.** A sequent `A ⊢ B` of strictly positive formulas is derivable in
RC iff every world satisfying `A` satisfies `B` in every Kripke model on an RC-frame. The source
proves this for the language with modalities in `ω + 1` (Beklemishev, "Positive provability logic
for uniform reflection principles", arXiv:1304.4396v3, Theorem 1(ii)); the restriction to
modalities in `ℕ` stated here follows from it with the conservativity of RC over its fragments
(Theorem 2 there), since an RC-model restricts to a model on an RC-frame for `ℕ`. The direction
from left to right is the proved `Derives.sound`. -/
theorem_wanted derives_iff_forall_frame {Atom : Type u} (A B : Formula Atom) :
    Derives A B ↔
      ∀ (W : Type u) (R : ℕ → W → W → Prop) (V : W → Atom → Prop), IsFrame R →
        ∀ x, Satisfies R V x A → Satisfies R V x B

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
