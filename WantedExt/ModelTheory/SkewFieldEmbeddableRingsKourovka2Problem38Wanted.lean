/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite axiomatizability of rings embeddable in skew fields (Kourovka Notebook Problem 2.38)

Kourovka Notebook, Archive of Solved Problems, Problem 2.38 (A. I. Mal'cev; old problem): the class
of rings embeddable in associative division rings is universally axiomatizable. Is it finitely
axiomatizable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.Defs
public import Mathlib.ModelTheory.Algebra.Ring.Basic

@[expose] public section

namespace MathlibExt.ModelTheory.SkewFieldEmbeddableRingsKourovka2Problem38Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.38 (A. I.
Mal'cev; old problem). UnsolvedMath record UM-00700111 (`KOU-2.38`), dataset ulamai/UnsolvedMath
v1.8.0.

Rings are associative with `1` (Cohn's setting) and embeddings are injective unital ring
homomorphisms into a division ring. A class of rings is finitely axiomatizable when it is the class
of rings satisfying a finite set of first-order sentences in Mathlib's language of rings
`Language.ring` (`+`, `*`, `-`, `0`, `1`), each ring carrying its canonical structure
`FirstOrder.Ring.compatibleRingOfRing`.
-/

open FirstOrder FirstOrder.Language

/-- Kourovka 2.38 (A. I. Mal'cev): the class of (associative, unital) rings embeddable in a
division ring is finitely axiomatizable: some finite set `T` of first-order sentences in the
language of rings holds in a ring `R` exactly when `R` admits an injective ring homomorphism into
a division ring. -/
def skewFieldEmbeddableRingsFinitelyAxiomatizable : Prop :=
  ∃ T : Language.ring.Theory, T.Finite ∧
    ∀ (R : Type) [Ring R],
      (letI := FirstOrder.Ring.compatibleRingOfRing R; R ⊨ T) ↔
        ∃ (D : Type) (_ : DivisionRing D) (f : R →+* D), Function.Injective f

/--
Resolved false: the Kourovka Archive answers 2.38 "No", citing Cohn (1974), who proved that the
class of rings embeddable in skew fields, universally axiomatizable by Mal'cev, is not finitely
axiomatizable. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
2.38 (A. I. Mal'cev; old problem); resolution: P. M. Cohn, The class of rings embeddable in skew
fields, Bull. London Math. Soc. 6 (1974), 147-148, Kourovka Archive, Problem 2.38: No (Cohn);
Encyclopedia of Mathematics, Imbedding of rings: the class of associative rings imbeddable in
skew-fields is not finitely axiomatized [Cohn 1974], https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted skewFieldEmbeddableRingsFinitelyAxiomatizable_refuted :
    ¬ skewFieldEmbeddableRingsFinitelyAxiomatizable

end MathlibExt.ModelTheory.SkewFieldEmbeddableRingsKourovka2Problem38Wanted
