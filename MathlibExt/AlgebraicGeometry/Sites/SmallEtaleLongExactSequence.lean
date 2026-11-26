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
# Long exact cohomology windows on small étale sites

For a short exact sequence of abelian sheaves in coefficient universe `max u w`, the
cohomology maps and connecting map give the six-term exact window from degree `n` to degree `n
+ 1`. The first degree-zero cohomology map is injective.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections
variable {X : Scheme.{u}}
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})}

/-- Six term small étale cohomology window.

For a short exact sheaf sequence, form its three cohomology objects in degree `n`, the
connecting map, and its three objects in degree `n + 1`. -/
def smallEtaleLongSequence (hS : S.ShortExact) (n : ℕ) :
    ComposableArrows AddCommGrpCat.{max u w} 5 :=
  Sheaf.H.longSequence hS n (n + 1) rfl

/-- Small étale cohomology windows are exact.

The six-term window of every short exact sheaf sequence is exact in every natural degree. -/
theorem smallEtaleLongSequence_exact (hS : S.ShortExact) (n : ℕ) :
    (smallEtaleLongSequence hS n).Exact :=
  Sheaf.H.longSequence_exact hS n (n + 1) rfl

/-- Initial degree zero cohomology map is injective.

For a short exact sheaf sequence, the degree-zero cohomology map of its first arrow is
injective. -/
theorem smallEtaleLongSequence_initial_injective (hS : S.ShortExact) :
    Function.Injective (Sheaf.H.map S.f 0) := by
  let := hS.mono_f
  exact Ext.postcomp_mk₀_injective_of_mono (integralSheaf.{u, w} X) S.f



/-- Exact cohomology windows with an initial injection.

Every adjacent-degree window of a short exact sheaf sequence is exact, and its first degree-
zero map is injective. -/
theorem original_small_etale_long_exact_sequence (hS : S.ShortExact) :
    (∀ n, (smallEtaleLongSequence hS n).Exact) ∧
      Function.Injective (Sheaf.H.map S.f 0) := by
  have hExact : ∀ n : ℕ, (smallEtaleLongSequence.{u, w} hS n).Exact :=
    fun n => smallEtaleLongSequence_exact.{u, w} (X := X) (S := S) hS n
  have hInitial : Function.Injective (Sheaf.H.map S.f 0) :=
    smallEtaleLongSequence_initial_injective.{u, w} (X := X) (S := S) hS
  exact And.intro hExact hInitial

end AlgebraicGeometry.Scheme.DerivedSections
