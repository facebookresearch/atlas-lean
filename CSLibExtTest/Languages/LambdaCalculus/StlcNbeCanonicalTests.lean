/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeCanonical

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.NbeCanonicalTests

open scoped CslibStlc

abbrev Atom := Ty.base (Base := Unit) ()

/-- The eta-long identity is already canonical. -/
example :
    normalizeTm
        ((.lam (.var .zero)) : Tm [] (Atom ⇒ Atom)) =
      (.lam (.var .zero) : Tm [] (Atom ⇒ Atom)) := by
  exact normalizeTm_toTm (.lam (.base (.var .zero)))

/-- Re-normalizing any term does not change its canonical representative. -/
example (t : Tm [Atom ⇒ Atom] (Atom ⇒ Atom)) :
    normalizeTm (normalizeTm t) = normalizeTm t := normalizeTm_idem t

/-- Forgetting the normal-form invariant and normalizing recovers the same
eta-long normal form. -/
example (n : Nf [Atom] (Atom ⇒ Atom)) : normalizeNf n.toTm = n :=
  normalizeNf_toTm n

/-- Reflection commutes with weakening into a larger context. -/
example (n : Ne [Atom] Atom) :
    Sem.rename (.succ : Ren [Atom] [Atom, Atom]) Atom (reflect Atom n) =
      reflect Atom (n.rename .succ) := reflect_rename Atom .succ n

/-- The fixed-point characterization exposes canonicality without requiring
clients to construct a normal-form witness by hand. -/
example (t : Tm [Atom] Atom) (h : normalizeTm t = t) : IsCanonical t :=
  (isCanonical_iff_normalizeTm_eq t).2 h

/-- A canonical term determines its eta-long normal form uniquely. -/
example (n m : Nf [Atom] Atom) (h : n.toTm = m.toTm) : n = m :=
  Nf.toTm_injective h

/-- The canonical equivalence round-trips normal forms. -/
example (n : Nf [Atom] (Atom ⇒ Atom)) :
    n.toCanonicalTm.toNf = n := CanonicalTm.toNf_toCanonicalTm n

#print axioms normalizeNf_toTm
#print axioms normalizeTm_idem
#print axioms normalizeTm_toTm
#print axioms isCanonical_iff_normalizeTm_eq
#print axioms CanonicalTm.toNf_toCanonicalTm

end Cslib.Languages.LambdaCalculus.Stlc.NbeCanonicalTests
