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

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.RightActions

/-! Public use of right outer actions with no ground algebra on S. -/

@[expose] public section

open MulOpposite TensorProduct.Balanced

universe k r s a b a' b'

namespace TensorProduct.Balanced.RightActionPublicApi

variable (K : Type k) (R : Type r) (S : Type s)
  [CommRing K] [Semiring R] [Semiring S]
  (A : Type a) (B : Type b) [AddCommGroup A] [AddCommGroup B]
  [Module K A] [Module K B] [Module Rᵐᵒᵖ A] [Module R B]
  [Module Sᵐᵒᵖ B] [SMulCommClass Sᵐᵒᵖ K B] [SMulCommClass R Sᵐᵒᵖ B]

-- S is arbitrary: there is no Algebra K S premise or commutativity of R/S.
example (s : Sᵐᵒᵖ) (a : A) (b : B) :
    letI := rightModule K R S A B
    s • mk K R A B a b = mk K R A B a (s • b) :=
  rightModule_smul_mk K R S A B s a b

-- The original ground action is retained by every computed outer scalar.
example :
    letI := rightModule K R S A B
    SMulCommClass Sᵐᵒᵖ K (TensorProduct.Balanced K R A B) :=
  rightSMulCommClass K R S A B

-- Multiplication in the opposite ring computes the actual successive action.
example (s t : Sᵐᵒᵖ) (a : A) (b : B) :
    rightAction K R S A B (s * t) (mk K R A B a b) =
      rightAction K R S A B s (rightAction K R S A B t (mk K R A B a b)) := by
  rw [map_mul]
  rfl

variable {K R S A B}
  {A' : Type a'} {B' : Type b'} [AddCommGroup A'] [AddCommGroup B']
  [Module K A'] [Module K B'] [Module Rᵐᵒᵖ A'] [Module R B']
  [Module Sᵐᵒᵖ B'] [SMulCommClass Sᵐᵒᵖ K B'] [SMulCommClass R Sᵐᵒᵖ B']

example (f : A →ₗ[K] A') (g : B →ₗ[K] B')
    (hf : ∀ (r : R) (a : A), f (op r • a) = op r • f a)
    (hg : ∀ (r : R) (b : B), g (r • b) = r • g b)
    (hs : ∀ (s : Sᵐᵒᵖ) (b : B), g (s • b) = s • g b) (a : A) (b : B) :
    letI := rightModule K R S A B
    letI := rightModule K R S A' B'
    mapRight f g hf hg hs (mk K R A B a b) = mk K R A' B' (f a) (g b) :=
  mapRight_mk f g hf hg hs a b

end TensorProduct.Balanced.RightActionPublicApi
