/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlagStage
public import MathlibExt.KTheory.Exact.Quillen.Basic

/-!
# Quillen spans from nested intervals in an admissible-mono flag

Four nested stages `a ≤ b ≤ c ≤ d` determine the admissible Quillen span

```text
[b,c]  ←↞  [a,c]  ↪  [a,d],
```

where `[i,j]` is the quotient interval of the flag.  Both legs are existing
interval maps.  Their admissibility follows directly from the two relevant
interval exact sequences.

This is the raw span used by the Segal-subdivision map into the Quillen
Q-construction.  No identity, composition, quotient descent, subdivision,
nerve, or realization claim is made here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open AlgebraicKTheory

universe v u

namespace CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  {n : ℕ} (F : AdmissibleMonoFlag C n)

/-- The Quillen span associated to four nested flag indices:
`[b,c] ←↞ [a,c] ↪ [a,d]`. -/
noncomputable def intervalQuillenSpan
    {a b c d : Fin (n + 1)}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    QuillenSpan
      (F.intervalQuotient b c hbc)
      (F.intervalQuotient a d ((hab.trans hbc).trans hcd)) where
  apex := F.intervalQuotient a c (hab.trans hbc)
  l := F.intervalMap (hab.trans hbc) hbc hab le_rfl
  r := F.intervalMap (hab.trans hbc)
    ((hab.trans hbc).trans hcd) le_rfl hcd
  wl := isAdmissibleEpi_g (F.interval_triple_exact hab hbc)
  wr := isAdmissibleMono_f
    (F.interval_triple_exact (hab.trans hbc) hcd)

@[simp]
theorem intervalQuillenSpan_apex
    {a b c d : Fin (n + 1)}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (F.intervalQuillenSpan hab hbc hcd).apex =
      F.intervalQuotient a c (hab.trans hbc) :=
  rfl

@[simp]
theorem intervalQuillenSpan_l
    {a b c d : Fin (n + 1)}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (F.intervalQuillenSpan hab hbc hcd).l =
      F.intervalMap (hab.trans hbc) hbc hab le_rfl :=
  rfl

@[simp]
theorem intervalQuillenSpan_r
    {a b c d : Fin (n + 1)}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (F.intervalQuillenSpan hab hbc hcd).r =
      F.intervalMap (hab.trans hbc)
        ((hab.trans hbc).trans hcd) le_rfl hcd :=
  rfl

/-- The interval map that changes neither endpoint is the identity. -/
theorem intervalMap_self
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    F.intervalMap hij hij le_rfl le_rfl =
      𝟙 (F.intervalQuotient i j hij) := by
  let _ : Epi (F.intervalπ i j hij) :=
    (isAdmissibleEpi_g (F.interval_exact i j hij)).epi
  apply (cancel_epi (F.intervalπ i j hij)).1
  rw [F.intervalπ_naturality hij hij le_rfl le_rfl]
  simp

/-- The quotient interval of an isomorphism in the flag is zero. -/
theorem intervalQuotient_isZero_of_isIso
    {i j : Fin (n + 1)} (hij : i ≤ j)
    [IsIso (F.chain.map (homOfLE hij))] :
    IsZero (F.intervalQuotient i j hij) :=
  CokernelCofork.IsColimit.isZero_of_epi
    (isColimit_cokernelCofork_of_isAdmissibleExact
      (F.interval_exact i j hij))

end CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlag

end
