/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Limits
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Colimits

/-!
# Complete and cocomplete marked carriers at the original size bounds

The explicit projection and image markings provide limits and colimits
for every shape for which the original simplicial carriers have them.
In particular, the marked category has all small limits and colimits at
its own value universe. This does not assert local presentability or a
marked model structure.
-/

universe u v w
open CategoryTheory CategoryTheory.Limits

namespace SSet.Marked

/-- Original simplicial limits provide marked limits at the same diagram size. -/
instance hasLimitsOfShape {J : Type w} [Category.{v} J]
    [HasLimitsOfShape J SSet.{u}] : HasLimitsOfShape J Marked.{u} where
  has_limit _ := inferInstance

/-- Original simplicial colimits provide marked colimits at the same diagram size. -/
instance hasColimitsOfShape {J : Type w} [Category.{v} J]
    [HasColimitsOfShape J SSet.{u}] : HasColimitsOfShape J Marked.{u} where
  has_colimit _ := inferInstance

/-- The marked category has all limits small in its original value universe. -/
instance hasSmallLimits : HasLimitsOfSize.{u, u} Marked.{u} where
  has_limits_of_shape _ := inferInstance

/-- It has all colimits at those same original smallness bounds. -/
instance hasSmallColimits : HasColimitsOfSize.{u, u} Marked.{u} where
  has_colimits_of_shape _ := inferInstance

end SSet.Marked
