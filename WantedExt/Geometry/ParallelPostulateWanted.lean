/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Independence of the parallel postulate

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.ParallelPostulate` — parallel_postulate_independent (manifest `manifests/problems/parallel_postulate_independent.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.ParallelPostulateWanted` namespace. Mathematical
statements are unchanged. Source: Independence of Euclid's parallel postulate; the hyperbolic-plane models are due to E. Beltrami (1868) and F. Klein (1871). Tarski's axiomatization: W. Schwabhäuser, W. Szmielew, A. Tarski, Metamathematische Methoden in der Geometrie, Springer (1983). Formalized in HOL Light by John Harrison and in Isabelle by Tim Makarios (T.J.M. Makarios, A Mechanical Verification of the Independence of Tarski's Euclidean Axiom, MSc thesis, Victoria University of Wellington, 2012; Isabelle/AFP entry Tarskis_Geometry).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace MathlibExt.Geometry.ParallelPostulateWanted
namespace Geometry

/-!
# Independence of the parallel postulate

Theorem #12 on Freek Wiedijk's *Formalizing 100 Theorems* list
(<https://www.cs.ru.nl/~freek/100/>). Euclid's parallel postulate is
logically independent of the remaining axioms of plane geometry: there is a
model of absolute (neutral) geometry in which the postulate holds and one in
which it fails, so neither it nor its negation follows from the other axioms.

We use Tarski's axiomatization. `TarskiAbsolute` bundles the betweenness (`B`)
and congruence (`C`) primitives with axioms `A1`–`A9` and the continuity
axiom `A11` — everything except the parallel postulate — following
Schwabhäuser–Szmielew–Tarski. The **Euclidean axiom** `A10` is kept separate
as a `Prop`. `parallel_postulate_independent` then asserts both that some
model satisfies `A10` (the real coordinate plane) and that some model refutes
it (the Klein–Beltrami disk model of the hyperbolic plane).

This formalization was cross-checked against the two existing formalizations
recorded on Freek's list:

* **HOL Light**, John Harrison — `Multivariate/tarski.ml` (axioms hold in
  `ℝ²`) and `100/independence.ml` (the Klein model satisfies `A1`–`A9`, `A11`
  but not `A10`). Axioms `A1`–`A10` match Harrison's `TARSKI_AXIOM_n`
  character-for-character; `A11` is Harrison's second-order continuity axiom.
* **Isabelle/AFP**, Tim Makarios — entry `Tarskis_Geometry`, which builds the
  Klein–Beltrami model and proves it satisfies every Tarski axiom except the
  Euclidean one.
-/

/-- A type carrying the **Tarski absolute-geometry signature** — a betweenness
relation `B` and a congruence relation `C` — satisfying axioms `A1`–`A9` and
`A11` (everything except the parallel postulate `A10`), following
Schwabhäuser–Szmielew–Tarski. -/
class TarskiAbsolute (M : Type*) where
  /-- Betweenness: `B a b c` says `b` lies between `a` and `c` (collinear; the
  non-strict convention, allowing `b = a` or `b = c`). -/
  B : M → M → M → Prop
  /-- Congruence of segments: `C a b c d` says `ab` is congruent to `cd`. -/
  C : M → M → M → M → Prop
  /-- **A1** Reflexivity of congruence. -/
  congr_refl : ∀ a b, C a b b a
  /-- **A2** Transitivity of congruence. -/
  congr_trans : ∀ a b c d e f, C a b c d → C a b e f → C c d e f
  /-- **A3** Identity of congruence: a zero-length segment has equal endpoints. -/
  congr_id : ∀ a b c, C a b c c → a = b
  /-- **A4** Segment construction: any segment can be extended to match a given length. -/
  segment_construction : ∀ a b c d, ∃ x, B a b x ∧ C b x c d
  /-- **A5** Five-segment axiom (a substitute for SAS congruence). -/
  five_segment : ∀ a b c d a' b' c' d', a ≠ b →
    B a b c → B a' b' c' →
    C a b a' b' → C b c b' c' → C a d a' d' → C b d b' d' →
    C c d c' d'
  /-- **A6** Identity of betweenness. -/
  betw_id : ∀ a b, B a b a → a = b
  /-- **A7** Inner Pasch. -/
  inner_pasch : ∀ a b c p q, B a p c → B b q c → ∃ x, B p x b ∧ B q x a
  /-- **A8** Lower-dimension axiom: there exist three non-collinear points. -/
  lower_dim : ∃ a b c, ¬ B a b c ∧ ¬ B b c a ∧ ¬ B c a b
  /-- **A9** Upper-dimension axiom (2D): three points equidistant from two
  distinct points are collinear. -/
  upper_dim : ∀ a b c p q, p ≠ q → C p a q a → C p b q b → C p c q c →
    B a b c ∨ B b c a ∨ B c a b
  /-- **A11** Continuity (second-order form): if some point `a` precedes the
  whole of `Y` as seen from `X` — every `x ∈ X` lies between `a` and every
  `y ∈ Y` — then some point `b` lies between every `x ∈ X` and every
  `y ∈ Y`. -/
  continuity : ∀ X Y : Set M,
    (∃ a, ∀ x ∈ X, ∀ y ∈ Y, B a x y) → (∃ b, ∀ x ∈ X, ∀ y ∈ Y, B x b y)

/-- The **Euclidean axiom** `A10` (Tarski's form of the parallel postulate,
equivalent to Euclid's fifth in the presence of the other axioms): for any
point `d` inside the angle `bac` and any point `t` on the ray from `a`
through `d`, the two sides of the angle, suitably extended, meet on a line
through `t`. -/
def Euclidean (M : Type*) (T : TarskiAbsolute M) : Prop :=
  ∀ a b c d t : M, T.B a d t → T.B b d c → a ≠ d →
    ∃ x y : M, T.B a b x ∧ T.B a c y ∧ T.B x t y

/- **Independence of the parallel postulate** (Freek #12). The Euclidean
axiom `A10` is logically independent of Tarski's absolute axioms `A1`–`A9`
and `A11`: there is a model of the absolute axioms in which the parallel
postulate holds (the real coordinate plane) and one in which it fails (the
Klein–Beltrami disk, or any other hyperbolic-plane model). -/
/-- Source: Independence of Euclid's parallel postulate; the hyperbolic-plane models are due to E. Beltrami (1868) and F. Klein (1871). Tarski's axiomatization: W. Schwabhäuser, W. Szmielew, A. Tarski, Metamathematische Methoden in der Geometrie, Springer (1983). Formalized in HOL Light by John Harrison and in Isabelle by Tim Makarios (T.J.M. Makarios, A Mechanical Verification of the Independence of Tarski's Euclidean Axiom, MSc thesis, Victoria University of Wellington, 2012; Isabelle/AFP entry Tarskis_Geometry). Via leanprover/lean-eval@38361be, problem `parallel_postulate_independent`. -/
public theorem_wanted parallel_postulate_independent :
    (∃ (M : Type) (T : TarskiAbsolute M), Euclidean M T) ∧
    (∃ (M : Type) (T : TarskiAbsolute M), ¬ Euclidean M T)

end Geometry

end MathlibExt.Geometry.ParallelPostulateWanted
