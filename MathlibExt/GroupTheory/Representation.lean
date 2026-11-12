/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Patrick Tam
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Character

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Algebra 511, Algebra 530

open CategoryTheory

/-!
# Character Degrees; Irreducible Character

## References

* This definition is found in the following paper by Donald White on page 2.
  https://www.math.kent.edu/~white/papers/autpsl2.pdf, If $G$ is any finite group,
  $\mathrm{Irr}(G)$ will denote the set of irreducible complex characters of $G$. We denote by
  $\mathrm{cd}(G) = \{ \chi (1), \chi \in \mathrm{Irr}(G) \}$ the set of character degrees of $G$.
  (for `cd`)
* "If $V$ is a representation of $G$, its character $\chi_V$ is the complex-valued function on the
  group defined by, \[, \chi_V (g) = \mathrm{Tr} (g|_V), \] the trace of $g$ on $V$.", This above
  definition is found on page 27 (page 13 on the white paper) as I retrieved it on October 15,
  2026:
  http://personal.cimat.mx:8181/~gil/docencia/2013/representaciones/fulton-harris-HQ-part1%2Bbib%2Bindex.pdf,
  Remark: Since we are dealing with Irreducible characters, we want to add the assumption that $V$
  is irreducible (for `IsIrrChar`)

## References

* This definition is found in the following paper by Donald White on page 2.
  https://www.math.kent.edu/~white/papers/autpsl2.pdf, If $G$ is any finite group,
  $\mathrm{Irr}(G)$ will denote the set of irreducible complex characters of $G$. We denote by
  $\mathrm{cd}(G) = \{ \chi (1), \chi \in \mathrm{Irr}(G) \}$ the set of character degrees of $G$.
  (for `cd`)
* "If $V$ is a representation of $G$, its character $\chi_V$ is the complex-valued function on the
  group defined by, \[, \chi_V (g) = \mathrm{Tr} (g|_V), \] the trace of $g$ on $V$.", This above
  definition is found on page 27 (page 13 on the white paper) as I retrieved it on October 15,
  2026:
  http://personal.cimat.mx:8181/~gil/docencia/2013/representaciones/fulton-harris-HQ-part1%2Bbib%2Bindex.pdf,
  Remark: Since we are dealing with Irreducible characters, we want to add the assumption that $V$
  is irreducible (for `IsIrrChar`)

## References

* This definition is found in the following paper by Donald White on page 2.
  https://www.math.kent.edu/~white/papers/autpsl2.pdf, If $G$ is any finite group,
  $\mathrm{Irr}(G)$ will denote the set of irreducible complex characters of $G$. We denote by
  $\mathrm{cd}(G) = \{ \chi (1), \chi \in \mathrm{Irr}(G) \}$ the set of character degrees of $G$.
  (for `cd`)
* "If $V$ is a representation of $G$, its character $\chi_V$ is the complex-valued function on the
  group defined by, \[, \chi_V (g) = \mathrm{Tr} (g|_V), \] the trace of $g$ on $V$.", This above
  definition is found on page 27 (page 13 on the white paper) as I retrieved it on October 15,
  2026:
  http://personal.cimat.mx:8181/~gil/docencia/2013/representaciones/fulton-harris-HQ-part1%2Bbib%2Bindex.pdf,
  Remark: Since we are dealing with Irreducible characters, we want to add the assumption that $V$
  is irreducible (for `IsIrrChar`)

## References

* This definition is found in the following paper by Donald White on page 2.
  https://www.math.kent.edu/~white/papers/autpsl2.pdf, If $G$ is any finite group,
  $\mathrm{Irr}(G)$ will denote the set of irreducible complex characters of $G$. We denote by
  $\mathrm{cd}(G) = \{ \chi (1), \chi \in \mathrm{Irr}(G) \}$ the set of character degrees of $G$.
  (for `cd`)
* "If $V$ is a representation of $G$, its character $\chi_V$ is the complex-valued function on the
  group defined by, \[, \chi_V (g) = \mathrm{Tr} (g|_V), \] the trace of $g$ on $V$.", This above
  definition is found on page 27 (page 13 on the white paper) as I retrieved it on October 15,
  2026:
  http://personal.cimat.mx:8181/~gil/docencia/2013/representaciones/fulton-harris-HQ-part1%2Bbib%2Bindex.pdf,
  Remark: Since we are dealing with Irreducible characters, we want to add the assumption that $V$
  is irreducible (for `IsIrrChar`)

## References

* This definition is found in the following paper by Donald White on page 2.
  https://www.math.kent.edu/~white/papers/autpsl2.pdf, If $G$ is any finite group,
  $\mathrm{Irr}(G)$ will denote the set of irreducible complex characters of $G$. We denote by
  $\mathrm{cd}(G) = \{ \chi (1), \chi \in \mathrm{Irr}(G) \}$ the set of character degrees of $G$.
  (for `cd`)
* "If $V$ is a representation of $G$, its character $\chi_V$ is the complex-valued function on the
  group defined by, \[, \chi_V (g) = \mathrm{Tr} (g|_V), \] the trace of $g$ on $V$.", This above
  definition is found on page 27 (page 13 on the white paper) as I retrieved it on October 15,
  2026:
  http://personal.cimat.mx:8181/~gil/docencia/2013/representaciones/fulton-harris-HQ-part1%2Bbib%2Bindex.pdf,
  Remark: Since we are dealing with Irreducible characters, we want to add the assumption that $V$
  is irreducible (for `IsIrrChar`)

## References

* This definition is found in the following paper by Donald White on page 2.
  https://www.math.kent.edu/~white/papers/autpsl2.pdf, If $G$ is any finite group,
  $\mathrm{Irr}(G)$ will denote the set of irreducible complex characters of $G$. We denote by
  $\mathrm{cd}(G) = \{ \chi (1), \chi \in \mathrm{Irr}(G) \}$ the set of character degrees of $G$.
  (for `cd`)
* "If $V$ is a representation of $G$, its character $\chi_V$ is the complex-valued function on the
  group defined by, \[, \chi_V (g) = \mathrm{Tr} (g|_V), \] the trace of $g$ on $V$.", This above
  definition is found on page 27 (page 13 on the white paper) as I retrieved it on October 15,
  2026:
  http://personal.cimat.mx:8181/~gil/docencia/2013/representaciones/fulton-harris-HQ-part1%2Bbib%2Bindex.pdf,
  Remark: Since we are dealing with Irreducible characters, we want to add the assumption that $V$
  is irreducible (for `IsIrrChar`)

## References

* This definition is found in the following paper by Donald White on page 2.
  https://www.math.kent.edu/~white/papers/autpsl2.pdf, If $G$ is any finite group,
  $\mathrm{Irr}(G)$ will denote the set of irreducible complex characters of $G$. We denote by
  $\mathrm{cd}(G) = \{ \chi (1), \chi \in \mathrm{Irr}(G) \}$ the set of character degrees of $G$.
  (for `cd`)
* "If $V$ is a representation of $G$, its character $\chi_V$ is the complex-valued function on the
  group defined by, \[, \chi_V (g) = \mathrm{Tr} (g|_V), \] the trace of $g$ on $V$.", This above
  definition is found on page 27 (page 13 on the white paper) as I retrieved it on October 15,
  2026:
  http://personal.cimat.mx:8181/~gil/docencia/2013/representaciones/fulton-harris-HQ-part1%2Bbib%2Bindex.pdf,
  Remark: Since we are dealing with Irreducible characters, we want to add the assumption that $V$
  is irreducible (for `IsIrrChar`)
-/

namespace MetaMathlibExt

-- Algebra 511: Character Degrees

/-- Let G be a finite group. Let Irr(G) will denote the set of irreducible complex characters of G.
We denote cd (G) = { χ (1) | χ ∈ Irr (G) }.
-/
def cd (G : Type) [Group G] [Fintype G] : Set ℕ :=
  {d | ∃ V : FDRep ℂ G, Simple V ∧ d = Module.finrank ℂ V}

-- Algebra 530: Irreducible Character

/-- If V is an irreducible representation of G, its character χ_V is the complex-valued function on
the group defined by

χ_V (g) = Tr (g|_V),

the trace of g on V.
-/
def IsIrrChar {G : Type*} [Group G] [Fintype G] (χ : G → ℂ) : Prop :=
  ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ ∀ g : G, χ g = FDRep.character V g

end MetaMathlibExt

end
