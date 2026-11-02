/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.AbelRuffini
public import Mathlib.GroupTheory.Solvable

@[expose] public section

/-!
# Roots of polynomials with Galois group `Sₙ` are not solvable by radicals

Mathlib proves one direction of the Abel–Ruffini theorem,
`isSolvable_gal_of_irreducible`: an irreducible polynomial with a root
solvable by radicals has a solvable Galois group. This module records the
contrapositive in its usable form: if the Galois group is the full symmetric
group `Sₙ` with `n ≥ 5`, then no root is solvable by radicals — in
particular, an irreducible polynomial with Galois group `S₅` has no root
solvable by radicals.

Source: `v1/Atlas/AlgebraNotes/code/GaloisTheory.lean`
(`GaloisTheory.not_solvableByRad_of_gal_iso_S5`), generalized from `n = 5`
to `n ≥ 5` via Mathlib's `Equiv.Perm.not_isSolvable`. The v1 proof used the
deprecated alias `solvable_of_surjective`; here the non-deprecated
`Group.isSolvable_of_surjective` is used instead.
-/

namespace GaloisTheory

/-- **Abel–Ruffini, contrapositive form.** Let $F$ be a field, let $E$ be a field extension of $F$,
and let $n \ge 5$. If $p \in F[X]$ is irreducible and the Galois group of $p$ over $F$ is isomorphic
to the symmetric group $S_n$, then no root of $p$ in $E$ is solvable by radicals over $F$. -/
theorem not_solvableByRad_of_gal_iso_perm {F E : Type*} [Field F] [Field E]
    [Algebra F E] {n : ℕ} (hn : 5 ≤ n) {p : Polynomial F} (hp : Irreducible p)
    (hiso : p.Gal ≃* Equiv.Perm (Fin n)) {x : E} (hpx : Polynomial.aeval x p = 0) :
    x ∉ solvableByRad F E := by
  intro hx
  have hsol : Group.IsSolvable p.Gal := isSolvable_gal_of_irreducible hx hp hpx
  -- Transport solvability along `hiso`, passing the `IsSolvable p.Gal`
  -- instance explicitly to avoid a `haveI` style-linter warning.
  have hsol' : Group.IsSolvable (Equiv.Perm (Fin n)) :=
    @Group.isSolvable_of_surjective _ _ _ _ hiso.toMonoidHom hiso.surjective hsol
  exact Equiv.Perm.not_isSolvable (X := Fin n) (by simpa using hn) hsol'

/-- **Abel–Ruffini for $S_5$.** Let $F$ be a field and let $E$ be a field extension of $F$. If
$p \in F[X]$ is irreducible and the Galois group of $p$ over $F$ is isomorphic to the symmetric
group $S_5$, then no root of $p$ in $E$ is solvable by radicals over $F$.

Source: v1 statement `GaloisTheory.not_solvableByRad_of_gal_iso_S5`, restated with the
non-deprecated solvability transport. -/
theorem not_solvableByRad_of_gal_iso_S5 {F E : Type*} [Field F] [Field E]
    [Algebra F E] {p : Polynomial F} (hp : Irreducible p)
    (hiso : p.Gal ≃* Equiv.Perm (Fin 5)) {x : E} (hpx : Polynomial.aeval x p = 0) :
    x ∉ solvableByRad F E :=
  not_solvableByRad_of_gal_iso_perm (by norm_num) hp hiso hpx

end GaloisTheory
