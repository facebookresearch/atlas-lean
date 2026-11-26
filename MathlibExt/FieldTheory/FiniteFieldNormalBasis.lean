/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Galois.Basic

import Mathlib.FieldTheory.Galois.NormalBasis

/-!
# Normal bases for finite field extensions

## References

- Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
  Journal of Integer Sequences 29 (2026), Article 26.4.6, pp. 1–31, Theorem 27.
- Mathlib, `Mathlib.FieldTheory.Galois.NormalBasis`,
  `exists_linearIndependent_algEquiv_apply`.
-/

namespace MetaMathlibExt

-- Keep the explicit finiteness hypotheses of the corrected wanted statement.
set_option linter.unusedFintypeInType false in
/-- **Normal basis theorem for finite fields.** Let $K$ be a finite field that is an algebra over
a finite field $F$. Then there is an element $\beta \in K$ whose images $\sigma(\beta)$, as $\sigma$
ranges over the $F$-algebra automorphisms of $K$, are linearly independent over $F$ (as a family
indexed by $\sigma$).

Since $K / F$ is Galois, there are $[K : F]$ such automorphisms, so these images form a basis of
$K$ over $F$, a normal basis.

Source: Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*,
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 27
(`jis-2026-26.4.6-thm-27`). -/
public theorem exists_normalBasis_finiteField (F K : Type*)
    [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K] :
    ∃ β : K, LinearIndependent F (fun σ : K ≃ₐ[F] K => σ β) :=
  exists_linearIndependent_algEquiv_apply F K

end MetaMathlibExt
