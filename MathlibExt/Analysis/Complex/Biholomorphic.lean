/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Babak Modami
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Analysis 418

/-!
# Biholomorphic map between domains

## References

* https://en.wikipedia.org/wiki/Biholomorphism (for `IsBiholomorphicOn`)

## References

* https://en.wikipedia.org/wiki/Biholomorphism (for `IsBiholomorphicOn`)

## References

* https://en.wikipedia.org/wiki/Biholomorphism (for `IsBiholomorphicOn`)

## References

* https://en.wikipedia.org/wiki/Biholomorphism (for `IsBiholomorphicOn`)

## References

* https://en.wikipedia.org/wiki/Biholomorphism (for `IsBiholomorphicOn`)

## References

* https://en.wikipedia.org/wiki/Biholomorphism (for `IsBiholomorphicOn`)

## References

* https://en.wikipedia.org/wiki/Biholomorphism (for `IsBiholomorphicOn`)
-/

namespace MetaMathlibExt

-- Analysis 418: Biholomorphic map between domains

/-- Let S, T ⊆ ℂ be open sets. If f : S → T is a holomorphic, injective and surjective map with
holomorphic inverse g, then f is a biholomorphic map between S and T.
-/
def IsBiholomorphicOn (f : ℂ → ℂ) (S T : Set ℂ) : Prop :=
  IsOpen S ∧ IsOpen T ∧
  DifferentiableOn ℂ f S ∧
  Set.InjOn f S ∧
  f '' S = T ∧
  ∃ g : ℂ → ℂ, DifferentiableOn ℂ g T ∧
    Set.BijOn g T S ∧
    (∀ z ∈ S, g (f z) = z) ∧
    (∀ w ∈ T, f (g w) = w)

end MetaMathlibExt

end
