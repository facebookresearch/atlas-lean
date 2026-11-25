/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleConnectingMaps

/-!
# Long exact sequences on small étale sites

Adjacent-degree windows use cohomology maps and extension-class connecting
maps. The initial monomorphism supplies the leading zero term in degree
zero.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections
variable {X : Scheme.{u}}
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})}

/-- The same canonical five arrows in every pair of adjacent degrees. -/
def smallEtaleLongSequence (hS : S.ShortExact) (n : ℕ) :
    ComposableArrows AddCommGrpCat.{max u w} 5 :=
  Sheaf.H.longSequence hS n (n + 1) rfl

/-- Exactness at all three kinds of places in each adjacent-degree window. -/
theorem smallEtaleLongSequence_exact (hS : S.ShortExact) (n : ℕ) :
    (smallEtaleLongSequence hS n).Exact :=
  Sheaf.H.longSequence_exact hS n (n + 1) rfl

/-- The degree-zero map is injective, by the actual integral-sheaf Hom functor
and the original sequence's first monomorphism. -/
theorem smallEtaleLongSequence_initial_injective (hS : S.ShortExact) :
    Function.Injective (Sheaf.H.map S.f 0) := by
  let := hS.mono_f
  exact Ext.postcomp_mk₀_injective_of_mono (integralSheaf.{u, w} X) S.f



/-- The complete all-degree sequence, including its initial zero term. -/
theorem original_small_etale_long_exact_sequence (hS : S.ShortExact) :
    (∀ n, (smallEtaleLongSequence hS n).Exact) ∧
      Function.Injective (Sheaf.H.map S.f 0) :=
  ⟨smallEtaleLongSequence_exact hS, smallEtaleLongSequence_initial_injective hS⟩

end AlgebraicGeometry.Scheme.DerivedSections
