/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Unions of chains of pure free summands (Kourovka Notebook Problem 2.4)

Kourovka Notebook, Archive of Solved Problems, Problem 2.4 (Yu. A. Bogan; question of S. Chase):
suppose that an abelian group `A` can be written as the union of pure subgroups `A_α`, `α ∈ Ω`,
where `Ω` is the first non-denumerable ordinal, `A_α` is a free abelian group of denumerable rank,
and, if `β < α`, then `A_β` is a direct summand of `A_α`. Does it follow that `A` is a free abelian
group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.SetTheory.Cardinal.Aleph
public import WantedExt.GroupTheory.PureSubgroupShared

@[expose] public section

namespace MathlibExt.GroupTheory.UnionOfPureFreeSummandsKourovka2Problem4Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.4 (Yu. A.
Bogan; question of S. Chase). UnsolvedMath record UM-00700083 (`KOU-2.4`), dataset
ulamai/UnsolvedMath v1.8.0.

The chain is indexed by the ordinals `α < ω₁` (`Ordinal.omega 1`); a function on all ordinals is
used and only its values below `ω₁` matter. Pure means `nA ∩ A_α = nA_α` for every integer `n`
(`IsPureSubgroup` of `PureSubgroupShared`);
denumerable rank means `Module.rank ℤ A_α = ℵ₀`; free abelian means `Module.Free ℤ`.
-/

open MathlibExt.GroupTheory.PureSubgroupShared (IsPureSubgroup)

/-- `S` is a direct summand of `T`: `T` is the internal direct sum of `S` and some `C`. -/
def IsDirectSummandOf {A : Type} [AddCommGroup A] (S T : AddSubgroup A) : Prop :=
  ∃ C : AddSubgroup A, S ⊓ C = ⊥ ∧ S ⊔ C = T

/-- Kourovka 2.4 (S. Chase; Yu. A. Bogan): if an abelian group `A` is the union of pure subgroups
`A_α`, `α < ω₁`, each free abelian of countably infinite rank, with `A_β` a direct summand of
`A_α` for `β < α`, then `A` is free abelian. -/
def unionOfPureFreeSummandsIsFree : Prop :=
  ∀ (A : Type) [AddCommGroup A] (S : Ordinal.{0} → AddSubgroup A),
    (∀ α < Ordinal.omega 1, IsPureSubgroup (S α) ∧ Module.Free ℤ (S α) ∧
      Module.rank ℤ (S α) = Cardinal.aleph0) →
    (∀ β α, β < α → α < Ordinal.omega 1 → IsDirectSummandOf (S β) (S α)) →
    (∀ a : A, ∃ α < Ordinal.omega 1, a ∈ S α) →
    Module.Free ℤ A

/--
Resolved false: the Kourovka Archive answers 2.4 "Not always", citing Griffith (1969), whose Theorem
2.2 constructs, for every ring that is not left perfect (for instance `ℤ`), an `ℵ₁`-separable module
that is the union of an `ω₁`-chain of countably generated submodules, each successor term a direct
summand, and is not a direct sum of countably generated modules, hence (for `ℤ`) not free. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.4 (Yu. A. Bogan;
question of S. Chase); resolution: P. A. Griffith, A note on a theorem of Hill, Pacific J. Math. 29
(1969), 279-284, Kourovka Archive, Problem 2.4: Not always (Griffith); Griffith's Theorem 2.2 and
its proof: for a ring that is not left perfect, such as ℤ, the union of a chain G_α, α < Ω, of
countably generated submodules of a product of copies of R with each G_{γ+1} a direct summand of the
union, which is not a direct sum of countably generated modules,
https://msp.org/pjm/1969/29-2/pjm-v29-n2-p06-p.pdf.
-/
public theorem_wanted unionOfPureFreeSummandsIsFree_refuted : ¬ unionOfPureFreeSummandsIsFree

end MathlibExt.GroupTheory.UnionOfPureFreeSummandsKourovka2Problem4Wanted
