/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exact rows of a quasi-isomorphic coaugmentation

In an abelian category, a coaugmentation `X[0] → I` that is a
quasi-isomorphism in degree zero gives an exact row `X → I⁰ → I¹`
and a monic first map. A full coaugmentation quasi-isomorphism also
gives exactness of all positive rows.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In an abelian category `C`, let `ι : X[0] → I` be a
coaugmentation of a nonnegative cochain complex and a quasi-isomorphism
in degree zero. The row `X → I⁰ → I¹` is exact, and `ι⁰` is mono. -/
theorem coaugmentation_exact_and_mono {X : C} {I : CochainComplex C ℕ}
    (ι : (single₀ C).obj X ⟶ I) [QuasiIsoAt ι 0] :
    (ShortComplex.mk (ι.f 0) (I.d 0 1)
      (by rw [ι.comm 0 1, HomologicalComplex.single_obj_d, zero_comp])).Exact ∧
      Mono (ι.f 0) := by
  have h := (quasiIsoAt₀_iff ι).mp inferInstance
  exact (ShortComplex.quasiIso_iff_of_zeros _
    (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 X 0 0)
    (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 X 0 1)
    (I.shape 0 0 (by simp [ComplexShape.up_Rel]))).mp h

/-- In an abelian category `C`, a coaugmentation quasi-isomorphism
`ι : X[0] → I` makes each row `Iⁿ → I^(n+1) → I^(n+2)` exact
at `I^(n+1)` for every `n ∈ ℕ`. -/
theorem coaugmentation_exact_succ {X : C} {I : CochainComplex C ℕ}
    (ι : (single₀ C).obj X ⟶ I) [QuasiIso ι] (n : ℕ) :
    (ShortComplex.mk (I.d n (n + 1)) (I.d (n + 1) (n + 2))
      (I.d_comp_d n (n + 1) (n + 2))).Exact := by
  have hI : I.ExactAt (n + 1) :=
    (exactAt_iff_of_quasiIsoAt ι (n + 1)).mp
      (exactAt_succ_single_obj X n)
  exact (HomologicalComplex.exactAt_iff' I n (n + 1) (n + 2)
    (by simp) (by simp)).mp hI

end CochainComplex
