/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Intersections of retracts of free groups with subgroups (Kourovka Notebook Problem 17.19)

Kourovka Notebook, Archive of Solved Problems, Problem 17.19 (G. M. Bergman): if `F` is a free group
of finite rank, `R` a retract of `F`, and `H` a subgroup of `F` of finite rank, must `H ∩ R` be a
retract of `H`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness

@[expose] public section

namespace MathlibExt.GroupTheory.RetractIntersectionFreeGroupKourovka17Problem19Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.19 (G. M.
Bergman). UnsolvedMath record UM-00701321 (`KOU-17.19`), dataset ulamai/UnsolvedMath v1.8.0.

`R` is a retract of `F` when some endomorphism of `F` has image `R` and fixes `R` pointwise. `F =
FreeGroup (Fin n)`; a subgroup of a free group has finite rank exactly when it is finitely
generated, so `H` is required to be finitely generated.
-/

/-- **Retract of a group.** A subgroup $R$ of a group $F$ is a retract of $F$ when there is an
endomorphism $r \colon F \to F$ whose image is $R$ and which fixes every element of $R$. -/
def IsRetract {F : Type*} [Group F] (R : Subgroup F) : Prop :=
  ∃ r : F →* F, r.range = R ∧ ∀ x ∈ R, r x = x

/-- **Bergman's retract intersection question (Kourovka Problem 17.19).** The statement that for
every natural number $n$, every retract $R$ of the free group $F_n$ on $n$ generators and every
finitely generated subgroup $H$ of $F_n$, the intersection $H \cap R$ is a retract of $H$.

A subgroup of a free group is finitely generated exactly when it has finite rank. -/
def retractIntersectionIsRetract : Prop :=
  ∀ (n : ℕ) (R H : Subgroup (FreeGroup (Fin n))), IsRetract R → H.FG →
    IsRetract ((H ⊓ R).subgroupOf H)

/--
**Negative answer to Bergman's retract intersection question (Kourovka Problem 17.19).** It is not
the case that for every natural number $n$, every retract $R$ of the free group $F_n$ on $n$
generators and every finitely generated subgroup $H$ of $F_n$, the intersection $H \cap R$ is a
retract of $H$.

Snopce, Tanushevski and Zalesskii (2022) give a free group $F$ of finite rank, a retract $R$ of $F$
and a finitely generated subgroup $H$ of $F$ such that $H \cap R$ is not a retract of $H$; the
Kourovka Archive answers 17.19 "No, it need not".

Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.19 (G. M. Bergman); resolution: I.
Snopce, S. Tanushevski and P. Zalesskii, Int. Math. Res. Notices 2022, no. 11 (2022), 8280-8294,
Kourovka Archive, Problem 17.19 (No, it need not).
-/
public theorem_wanted retractIntersectionIsRetract_refuted : ¬ retractIntersectionIsRetract

end MathlibExt.GroupTheory.RetractIntersectionFreeGroupKourovka17Problem19Wanted
