/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A counterexample to the unit conjecture for group rings

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.UnitConjecture` — annals_unit_conjecture (manifest `manifests/problems/annals_unit_conjecture.toml`, rev 1, submitter Thomas Browning, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.UnitConjectureWanted` namespace. Mathematical
statements are unchanged. Source: G. Gardam, `A counterexample to the unit conjecture for group rings`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-UnitConjecture.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.GroupTheory.UnitConjectureWanted
/-!
# Main Statement from A counterexample to the unit conjecture for group rings

We formalise the statement of the main result from G. Gardam,
`A counterexample to the unit conjecture for group rings`, Annals of Math, 194 (3) 2021.
-/

set_option autoImplicit false

noncomputable section

namespace UnitConjecture

/-- **Generators of Gardam's presentation.** This is the two-element set consisting of the
distinct formal symbols $a$ and $b$, which serve as the generators of the group presentation in
Theorem A of Gardam's counterexample to the unit conjecture. -/
inductive generators where
  | a
  | b

/-- **First free generator of Gardam's presentation.** $a$ is the generator $a$, viewed as an
element of the free group on the two generators $a$ and $b$. -/
def a : FreeGroup generators := .of generators.a

/-- **Second free generator of Gardam's presentation.** $b$ is the generator $b$, viewed as an
element of the free group on the two generators $a$ and $b$. -/
def b : FreeGroup generators := .of generators.b

/-- **Relators of Gardam's group.** In the free group on the generators $a$ and $b$, the relators
are the two elements $b^{-1}a^2ba^2$ and $a^{-1}b^2ab^2$.

Imposing them gives the relations $b^{-1}a^2b = a^{-2}$ and $a^{-1}b^2a = b^{-2}$ of Theorem A of
Gardam's counterexample to the unit conjecture. -/
def relations : Set (FreeGroup generators) :=
  {b⁻¹ * a ^ 2 * b * a ^ 2, a⁻¹ * b ^ 2 * a * b ^ 2}

/-- **Gardam's group.** $P$ is the group with generators $a$ and $b$ and relators
$b^{-1}a^2ba^2$ and $a^{-1}b^2ab^2$, that is,
$P = \langle a, b \mid b^{-1}a^2b = a^{-2}, a^{-1}b^2a = b^{-2} \rangle$.

This is the group of Theorem A of Gardam's counterexample to the unit conjecture. -/
def P := PresentedGroup relations
deriving Coe (FreeGroup generators), Group

/-- **The element x of Gardam's group.** In the group $P$ with presentation
$\langle a, b \mid b^{-1}a^2b = a^{-2},\ a^{-1}b^2a = b^{-2} \rangle$, $x = a^2$. -/
def x : P := a ^ 2

/-- **The element y of Gardam's group.** In the group $P$ with presentation
$\langle a, b \mid b^{-1}a^2b = a^{-2},\ a^{-1}b^2a = b^{-2} \rangle$, $y = b^2$. -/
def y : P := b ^ 2

/-- **The element z of Gardam's group.** In the group $P$ with presentation
$\langle a, b \mid b^{-1}a^2b = a^{-2},\ a^{-1}b^2a = b^{-2} \rangle$, $z = (ab)^2$. -/
def z : P := (a * b) ^ 2

/-- **Group ring of Gardam's group over the field with two elements.** $\mathbb{F}_2[P]$ is the
group ring of Gardam's group $P$ over the field $\mathbb{F}_2 = \mathbb{Z}/2\mathbb{Z}$. -/
abbrev R := MonoidAlgebra (ZMod 2) P

instance : Coe P R where
  coe := MonoidAlgebra.of (ZMod 2) P

/-- **Gardam's element p.** In the group ring $\mathbb{F}_2[P]$ of Gardam's group $P$ with
generators $a$ and $b$, let $x = a^2$, $y = b^2$ and $z = (ab)^2$ in $P$, viewed as elements of
$\mathbb{F}_2[P]$. Then $p$ is the element $(1 + x)(1 + y)(1 + z^{-1})$ of $\mathbb{F}_2[P]$. -/
def p : R := (1 + x) * (1 + y) * (1 + z⁻¹)

/-- **Gardam's element q.** In the group ring $\mathbb{F}_2[P]$ of Gardam's group $P$ with
generators $a$ and $b$, let $x = a^2$, $y = b^2$ and $z = (ab)^2$ in $P$, viewed as elements of
$\mathbb{F}_2[P]$. Then $q$ is the element $x^{-1}y^{-1} + x + y^{-1}z + z$ of $\mathbb{F}_2[P]$. -/
def q : R := x⁻¹ * y⁻¹ + x + y⁻¹ * z + z

/-- **Gardam's element r.** In the group ring $\mathbb{F}_2[P]$ of Gardam's group $P$ with
generators $a$ and $b$, let $x = a^2$, $y = b^2$ and $z = (ab)^2$ in $P$, viewed as elements of
$\mathbb{F}_2[P]$. Then $r$ is the element $1 + x + y^{-1}z + xyz$ of $\mathbb{F}_2[P]$. -/
def r : R := 1 + x + y⁻¹ * z + x * y * z

/-- **Gardam's element s.** In the group ring $\mathbb{F}_2[P]$ of Gardam's group $P$ with
generators $a$ and $b$, let $x = a^2$, $y = b^2$ and $z = (ab)^2$ in $P$, viewed as elements of
$\mathbb{F}_2[P]$. Then $s$ is the element $1 + (x + x^{-1} + y + y^{-1})z^{-1}$ of
$\mathbb{F}_2[P]$. -/
def s : R := 1 + (x + x⁻¹ + y + y⁻¹) * z⁻¹

/-- **Gardam's unit.** Let $P$ be the group with presentation
$\langle a, b \mid b^{-1}a^2b = a^{-2},\ a^{-1}b^2a = b^{-2} \rangle$ and set $x = a^2$,
$y = b^2$, $z = (ab)^2$. In the group ring $\mathbb{F}_2[P]$, $u = p + qa + rb + sab$, where
$p = (1 + x)(1 + y)(1 + z^{-1})$, $q = x^{-1}y^{-1} + x + y^{-1}z + z$,
$r = 1 + x + y^{-1}z + xyz$ and $s = 1 + (x + x^{-1} + y + y^{-1})z^{-1}$. -/
def u : R := p + q * a + r * b + s * (a * b)

/--
**Gardam's counterexample to the unit conjecture.** Let $P$ be the group with presentation
$\langle a, b \mid b^{-1}a^2b = a^{-2},\ a^{-1}b^2a = b^{-2} \rangle$, and set $x = a^2$,
$y = b^2$ and $z = (ab)^2$. In the group ring $\mathbb{F}_2[P]$ set
$p = (1 + x)(1 + y)(1 + z^{-1})$, $q = x^{-1}y^{-1} + x + y^{-1}z + z$,
$r = 1 + x + y^{-1}z + xyz$ and $s = 1 + (x + x^{-1} + y + y^{-1})z^{-1}$, and let
$u = p + qa + rb + sab$. Then $P$ is torsion-free (if $g \in P$ and $g^n = 1$ for some
natural number $n \neq 0$, then $g = 1$), $u$ is a unit of $\mathbb{F}_2[P]$, and $u$ is not
equal to any element $g$ of $P$ viewed in $\mathbb{F}_2[P]$; that is, $u$ is a non-trivial unit.

Source: G. Gardam, `A counterexample to the unit conjecture for group rings`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-UnitConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_unit_conjecture`.
-/
public theorem_wanted theorem_A : (∀ g : P, ∀ n ≠ 0, g ^ n = 1 → g = 1) ∧ IsUnit u ∧ ¬ ∃ g : P, u = g

end UnitConjecture

end

end MathlibExt.GroupTheory.UnitConjectureWanted
