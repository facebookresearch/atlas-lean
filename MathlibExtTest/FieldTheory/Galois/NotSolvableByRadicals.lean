/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.Galois.NotSolvableByRadicals
import Mathlib.Tactic

namespace MathlibExtTest.FieldTheory.Galois.NotSolvableByRadicals

open GaloisTheory

/-- The `n = 6` instance of the general theorem: a root of an irreducible
polynomial with Galois group `S₆` is not solvable by radicals. -/
example {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p : Polynomial F} (hp : Irreducible p) (hiso : p.Gal ≃* Equiv.Perm (Fin 6))
    {x : E} (hpx : Polynomial.aeval x p = 0) :
    x ∉ solvableByRad F E :=
  not_solvableByRad_of_gal_iso_perm (by norm_num) hp hiso hpx

/-- The `S₅` instance: a root of an irreducible polynomial with Galois
group `S₅` is not solvable by radicals. -/
example {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p : Polynomial F} (hp : Irreducible p) (hiso : p.Gal ≃* Equiv.Perm (Fin 5))
    {x : E} (hpx : Polynomial.aeval x p = 0) :
    x ∉ solvableByRad F E :=
  not_solvableByRad_of_gal_iso_S5 hp hiso hpx

/-- Contrapositive: if a root of an irreducible polynomial *is* solvable by
radicals, then its Galois group cannot be `S₅`. -/
example {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p : Polynomial F} (hp : Irreducible p) {x : E} (hpx : Polynomial.aeval x p = 0)
    (hx : x ∈ solvableByRad F E) :
    ¬ Nonempty (p.Gal ≃* Equiv.Perm (Fin 5)) := by
  rintro ⟨hiso⟩
  exact not_solvableByRad_of_gal_iso_S5 hp hiso hpx hx

/-- The same contrapositive at `n = 7`: solvability by radicals of a root
rules out Galois group `S₇`. -/
example {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p : Polynomial F} (hp : Irreducible p) {x : E} (hpx : Polynomial.aeval x p = 0)
    (hx : x ∈ solvableByRad F E) :
    ¬ Nonempty (p.Gal ≃* Equiv.Perm (Fin 7)) := by
  rintro ⟨hiso⟩
  exact not_solvableByRad_of_gal_iso_perm (by norm_num) hp hiso hpx hx

end MathlibExtTest.FieldTheory.Galois.NotSolvableByRadicals
