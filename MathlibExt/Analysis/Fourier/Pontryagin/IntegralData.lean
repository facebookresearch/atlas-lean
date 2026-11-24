/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Fourier.PontryaginDualIntegral
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.CompactSupport
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The original general LCA character Fourier integral

For the true compact-open Pontryagin dual and an original left Haar measure,
use the literal integral of conjugate chi(s) times f(s). Compact-supported
scalar functions retain the existing actual Haar L2 inclusion. Integrability
and the L1 bound use only the original scalar character norm and compact
support. No finite/Euclidean Plancherel model, dual measure normalization,
Fourier equivalence or C0-range conclusion is supplied or chosen as DATA.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped CompactlySupported

namespace PontryaginDual

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (mu : Measure G) [mu.IsHaarMeasure] [mu.Regular]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [mu.Regular] in
/-- Every literal original compact-supported Fourier kernel is Haar integrable. -/
theorem integrable_haarFourierKernel (f : C_c(G, ℂ)) (chi : PontryaginDual G) :
    Integrable (fun s : G => star (chi s : ℂ) * f s) mu := by
  have hcontinuous : Continuous (fun s : G => star (chi s : ℂ) * f s) :=
    (continuous_subtype_val.comp (map_continuous chi)).star.mul (map_continuous f)
  have hcompact : HasCompactSupport (fun s : G => star (chi s : ℂ) * f s) :=
    HasCompactSupport.intro' f.hasCompactSupport (isClosed_tsupport f) (fun s hs => by
      rw [image_eq_zero_of_notMem_tsupport hs, mul_zero])
  exact hcontinuous.integrable_of_hasCompactSupport hcompact

end PontryaginDual
