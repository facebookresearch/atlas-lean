/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.Topology.Category.CGWH.Colimits

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

example {I : Type v} (X : I → CGWH.{u, v}) (i : I) :
    Limits.Sigma.ι (fun j => CGWH.cgwhToTop.obj (X j)) i ≫
        (CGWH.coproductComparisonIso X).hom =
      CGWH.cgwhToTop.map (Limits.Sigma.ι X i) :=
  CGWH.coproductComparisonIso_ι X i
