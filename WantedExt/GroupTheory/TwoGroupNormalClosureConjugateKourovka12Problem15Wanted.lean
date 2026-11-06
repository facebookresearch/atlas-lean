/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite 2-groups in which equal normal closures force conjugacy (Kourovka Notebook Problem 12.15)

Kourovka Notebook, Problem 12.15 (E. A. Golikova, A. I. Starostin): suppose that in a finite 2-group
`G` any two elements are conjugate whenever their normal closures coincide. Is the derived subgroup
of `G` abelian?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.TwoGroupNormalClosureConjugateKourovka12Problem15Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 12.15 (E. A. Golikova, A. I. Starostin).
UnsolvedMath record UM-00700835 (`KOU-12.15`), dataset ulamai/UnsolvedMath v1.8.0.

The normal closure of `x` is `Subgroup.normalClosure {x}`; the derived subgroup is `commutator G`,
and abelian means its elements commute.
-/

/-- **Golikova–Starostin question on finite $2$-groups in which normal closures determine
conjugacy (Kourovka 12.15).** The statement that for every finite $2$-group $G$ in which any two
elements with the same normal closure are conjugate, the derived subgroup $G'$ of $G$ is
abelian. -/
def normalClosureConjDerivedAbelian : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsPGroup 2 G →
    (∀ x y : G, Subgroup.normalClosure {x} = Subgroup.normalClosure {y} → IsConj x y) →
    ∀ a ∈ commutator G, ∀ b ∈ commutator G, a * b = b * a

/--
**Equal normal closures forcing conjugacy does not make the derived subgroup of a finite $2$-group
abelian (Kourovka 12.15).** There exists a finite $2$-group $G$ in which any two elements with the
same normal closure are conjugate, but whose derived subgroup $G'$ is not abelian.

Muliarchyk gives an explicit such group of order $2^{11} = 2048$, given by a power-commutator
presentation, whose second derived subgroup $G'' = (G')'$ is nontrivial (a ChatGPT-assisted
construction with a symbolic proof); the Kourovka Notebook (21st issue) marks 12.15 solved, "No,
not always".

Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Problem 12.15 (E. A. Golikova, A. I. Starostin); resolution: K.
Muliarchyk, An explicit counterexample to Kourovka Notebook Problem 12.15, preprint (13 August
2026), main result: an explicit group of order `2¹¹ = 2048`, given by a power-commutator
presentation, satisfies the hypothesis and has `G'' = ⟨z⟩ ≠ 1`; the Kourovka Notebook (21st issue)
marks 12.15 solved,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/08/kourovka_12_15_counterexample.pdf.
-/
public theorem_wanted normalClosureConjDerivedAbelian_refuted : ¬ normalClosureConjDerivedAbelian

end MathlibExt.GroupTheory.TwoGroupNormalClosureConjugateKourovka12Problem15Wanted
