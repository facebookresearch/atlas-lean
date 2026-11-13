/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kazhdan's property (T) for Aut(F_n), n ≥ 5 (Bridson–Vogtmann, Question 2.4)

B. Farb (ed.), Problems on Mapping Class Groups and Related Topics, Ch. 20 (M. Bridson and K.
Vogtmann), Question 2.4: for `n > 3`, does `Aut(F_n)` have property (T)?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.OnPropertyTWanted

@[expose] public section

namespace MathlibExt.GroupTheory.AutFreeGroupPropertyTAMR109Problem0272Wanted

/-!
Source: B. Farb (ed.), Problems on Mapping Class Groups and Related Topics (2006), Ch. 20 (M.
Bridson and K. Vogtmann), Question 2.4. UnsolvedMath record UM-11000272 (`AMR-109-0272`), dataset
ulamai/UnsolvedMath v1.8.0.

`Aut(F_n)` is `MulAut (FreeGroup (Fin n))`. Property (T) is the predicate `PropertyT` of the
existing entry `WantedExt/GroupTheory/OnPropertyTWanted.lean`: a finite symmetric generating set `S`
and `λ > 0` with `Δ² - λΔ` a sum of hermitian squares in `ℝG`, `Δ = |S| - ∑ s` (Ozawa's
characterization of (T) for finitely generated groups, used by all three resolving papers). That
entry states the case `n ≥ 6`; this one adds `n = 5`. The case `n = 4` rests only on M. Nitsche's
computer proof (arXiv:2009.05134), which has no journal record (no Crossref entry, no arXiv
journal-ref, checked 2026-10-24), so it is not stated here: it is the open entry
`OpenConjectures/GroupTheory/AutF4PropertyT`.
-/

/-- Bridson–Vogtmann's question (Farb (ed.), Problems on Mapping Class Groups, Ch. 20, Question
2.4), answered for `n ≥ 5`: `Aut(F_n)` has Kazhdan's property (T) for every `n > 4`. Property (T)
is the predicate `PropertyT` of `WantedExt.GroupTheory.OnPropertyTWanted` (Ozawa's
characterization used in Kaluba–Kielak–Nowak, equation (2)). -/
def autFreeGroupPropertyT : Prop :=
  ∀ n : ℕ, 4 < n →
    MathlibExt.GroupTheory.OnPropertyTWanted.OnPropertyT.PropertyT (MulAut (FreeGroup (Fin n)))

/--
Resolved true for `n ≥ 5`: `Aut(F_n)` has property (T) for every `n > 4`: Kaluba–Nowak–Ozawa
(`n = 5`) and Kaluba–Kielak–Nowak (`n ≥ 6`), each by certifying an Ozawa sum-of-squares
decomposition of `Δ² - λΔ`. The case `n = 4` is claimed only by M. Nitsche's unrefereed computer
proof (arXiv:2009.05134, Theorem 6.1) and is the open entry `AutF4PropertyT`. Source: B. Farb (ed.),
Problems on Mapping Class Groups and Related Topics (2006), Ch. 20 (M. Bridson and K. Vogtmann),
Question 2.4; resolution: M. Kaluba, P. W. Nowak and N. Ozawa, Aut(F₅) has property (T), Math. Ann.
375 (2019), 1169-1191, arXiv:1712.07167 (n = 5); M. Kaluba, D. Kielak and P. W. Nowak, On property
(T) for Aut(F_n) and SL_n(ℤ), Ann. of Math. 193 (2021), arXiv:1812.03456 (n ≥ 6), KNO main theorem
(SAut(F₅) has (T), hence Aut(F₅)); KKN Theorem 1 (Aut(F_n) has (T) for n ≥ 6),
https://arxiv.org/abs/1812.03456.
-/
public theorem_wanted autFreeGroupPropertyT_holds : autFreeGroupPropertyT

end MathlibExt.GroupTheory.AutFreeGroupPropertyTAMR109Problem0272Wanted
