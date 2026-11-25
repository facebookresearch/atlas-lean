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

public import MathlibExt.Analysis.CStarAlgebra.Multiplier.Outer

/-!
# Busby homomorphism types

`BusbyHom A B` is the existing complex nonunital star-algebra homomorphism
type into the actual outer multiplier algebra of `B`. Its source needs only
the algebraic operations required by that type and its stock zero map.

`BusbyMap` retains the C-star source specialization used by concrete
extensions. The weak-source alias alone does not classify extensions, choose
a stable sum, or identify the coefficient with a stabilization.
-/

@[expose] public section

noncomputable section

namespace CStarExtension

universe uA uB

/-- **Busby homomorphisms.** Let `A` be a nonunital, possibly nonassociative semiring with a
distributive complex scalar action and an additive star operation, and let `B` be a nonunital
complex C*-algebra. A Busby homomorphism is a complex nonunital star homomorphism `A → M(B)/B`,
where `M(B)` is the multiplier algebra. -/
abbrev BusbyHom (A : Type uA) (B : Type uB)
    [NonUnitalNonAssocSemiring A] [DistribMulAction ℂ A] [StarAddMonoid A]
    [NonUnitalCStarAlgebra B] :=
  let _ : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  A →⋆ₙₐ[ℂ] OuterMultiplier B

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The C-star dictionary on the outer multiplier algebra, for local use. -/
noncomputable local instance outerCStarAlgebra :
    CStarAlgebra (OuterMultiplier B) :=
  outerMultiplierCStarAlgebra B

/-- **Busby map of C*-algebras.** For nonunital complex C*-algebras `A,B`, this is a nonunital complex
star homomorphism from `A` to the outer multiplier algebra `M(B)/B`, equipped with its quotient
C*-norm. -/
abbrev BusbyMap :=
  BusbyHom A B

end CStarExtension
