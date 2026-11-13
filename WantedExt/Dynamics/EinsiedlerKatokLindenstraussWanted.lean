/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Smallness of exceptional set to Littlewood's conjecture

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.EinsiedlerKatokLindenstrauss` — einsiedler_katok_lindenstrauss (manifest `manifests/problems/einsiedler_katok_lindenstrauss.toml`, rev 1, submitter Junyan Xu, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.EinsiedlerKatokLindenstraussWanted` namespace. Mathematical
statements are unchanged. Source:
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Dynamics.EinsiedlerKatokLindenstraussWanted
/-!
# Smallness of exceptional set to Littlewood's conjecture

Littlewood conjectured in the 1930s that liminf_{n→∞} n⟨nα⟩⟨nβ⟩=0 for any real numbers
α and β, where ⟨x⟩ is the distance from x to the nearest integer.

In 2003, Einsiedler, Katok and Lindenstrauss used ergodic methods to prove that the set of
exceptions to Littlewood’s conjecture is extremely small (has zero Hausdorff dimension).

The proof relies on a partial classification of certain invariant measures on SL₃(ℤ)\SL₃(ℝ).
This is part of the theory of measure rigidity, and the particular type of phenomenon seen
has its origins in work of Furstenberg. A special case of far-reaching conjectures by Margulis,
by Furstenberg, and by Katok concerns actions of the group A of positive diagonal matrices in
SLₖ(ℝ) for k ⩾ 3 on the space SLₖ(ℤ)\SLₖ(ℝ): if µ is an A-invariant ergodic probability measure
on this space, then it is homogeneous in the sense that there a closed connected group L ⩾ A
for which µ is the unique L-invariant measure on a single closed L-orbit. The work of Einsiedler,
Katok and Lindenstrauss proved this conjecture under the additional hypothesis that the measure
µ gives positive entropy to some one-parameter subgroup of A, which leads to the stated theorem.

## References

* M. Einsiedler, A. Katok, and E. Lindenstrauss, ‘Invariant measures and the set of
  exceptions to Littlewood’s conjecture’, Ann. of Math. (2) 164 (2006), no. 2, 513–560.

* Venkatesh, Akshay (2008). "The work of Einsiedler, Katok and Lindenstrauss on the Littlewood
  conjecture". Bulletin of the American Mathematical Society. 45 (1): 117–134.
  https://doi.org/10.1090/S0273-0979-07-01194-9.

* Manfred Einsiedler, Thomas Ward. Ergodic Theory: with a view towards Number Theory (GTM 259).
  London: Springer. 2010. https://doi.org/10.1007/978-0-85729-021-2
-/

namespace Dynamics.EinsiedlerKatokLindenstrauss

/-- **Distance to the nearest integer.** For a real number $x$, this is $|x - r|$, where $r$
is the integer nearest to $x$ (halves rounded up); equivalently, it is the minimum of
$|x - n|$ over all integers $n$. -/
noncomputable def distToNearestInt (x : ℝ) : ℝ := |x - round x|

/-- **Einsiedler–Katok–Lindenstrauss theorem.** For a real number $x$, write $\lVert x \rVert$
for the distance from $x$ to the nearest integer. The set of pairs $(\alpha, \beta)$ of real
numbers with $\liminf_{n \to \infty} n \cdot \lVert n\alpha \rVert \cdot \lVert n\beta \rVert > 0$,
the lower limit taken over natural numbers $n$, has Hausdorff dimension $0$ in $\mathbb{R}^2$.

Source: see manifest Via leanprover/lean-eval@38361be, problem `einsiedler_katok_lindenstrauss`. -/
public theorem_wanted einsiedler_katok_lindenstrauss :
    dimH {(α, β) : ℝ × ℝ | Filter.atTop.liminf
      (fun n : ℕ ↦ n * distToNearestInt (n * α) * distToNearestInt (n * β)) > 0} = 0

end Dynamics.EinsiedlerKatokLindenstrauss

end MathlibExt.Dynamics.EinsiedlerKatokLindenstraussWanted
