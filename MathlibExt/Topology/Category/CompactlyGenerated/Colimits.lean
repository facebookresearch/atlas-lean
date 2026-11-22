/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CompactlyGenerated.GeneratedBy
public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Colimits of compactly generated spaces

The inclusion of compactly generated spaces into topological spaces is
coreflective.  Since topological spaces have all small colimits, the generic
coreflective-subcategory theorem supplies same-universe-small colimits in
`CompactlyGenerated`.

This file installs only the canonical colimit instance.  It introduces no
second coreflector, chosen product, weak-Hausdorff reflection, or CGWH
construction.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Limits

namespace CompactlyGenerated

noncomputable instance instHasColimitsOfSize :
    HasColimitsOfSize.{v, v} CompactlyGenerated.{u, v} :=
  CategoryTheory.hasColimits_of_coreflective
    (C := TopCat.{v}) (D := CompactlyGenerated.{u, v})
    CompactlyGenerated.compactlyGeneratedToTop

end CompactlyGenerated
