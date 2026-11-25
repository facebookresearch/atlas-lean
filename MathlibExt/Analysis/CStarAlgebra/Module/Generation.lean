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

public import MathlibExt.Analysis.CStarAlgebra.Module.Standard

/-!
# Generation and direct-sum models for right C-star modules

This file defines countable generation by a right coefficient span and the
characteristic interface for a completed countable Hilbert-module direct sum.
The direct-sum interface is pinned by orthogonal coordinate inclusions and
density, without selecting an arbitrary equivalence.
-/

@[expose] public section

open Set
open scoped RightActions

namespace CStarModule

universe uB uE uX

variable {B : Type uB} {E : Type uE} {X : Type uX}
variable [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [SMul Bᵐᵒᵖ X]

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E be a
complete normed right inner-product module over B, with compatible complex normed-space
structures.

The module E is countably generated when some sequence in E has right coefficient multiples
whose complex-linear span is dense in E.
-/
def IsCountablyGenerated
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] : Prop :=
  ∃ g : ℕ → E,
    Dense (Submodule.span ℂ
      (Set.range fun p : ℕ × B ↦ g p.1 <• p.2) : Set E)

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and X be
complete normed right inner-product modules over B, with compatible complex normed-space
structures.

A family of bounded complex-linear inclusions E → X describes the completed countable direct sum
when the inclusions preserve the coefficient action and inner products, distinct coordinate
images are orthogonal, and the complex span of all coordinate images is dense in X.
-/
def IsCountableDirectSumModel
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
    [CStarModule Bᵐᵒᵖ X] [CompleteSpace X]
    (single : ℕ → E →L[ℂ] X) : Prop :=
  (∀ (i : ℕ) (x : E) (b : B),
    single i (x <• b) = single i x <• b) ∧
  (∀ (i j : ℕ) (x y : E),
    rightInner (B := B) (single i x) (single j y) =
      if i = j then rightInner (B := B) x y else 0) ∧
  Dense (Submodule.span ℂ
    (Set.range fun p : ℕ × E ↦ single p.1 p.2) : Set X)

end CStarModule
