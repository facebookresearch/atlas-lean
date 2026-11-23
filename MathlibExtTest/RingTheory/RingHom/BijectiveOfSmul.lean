/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.RingHom.BijectiveOfSmul

/-! # Consumers for `RingHom.bijective_of_surjective_of_smul_eq` -/

namespace RingHomBijectiveOfSmulTest

/-- The exact source statement, with no added hypothesis. -/
public theorem exactSource {S T N : Type*} [CommRing S] [Ring T]
    [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N]
    [Nontrivial N] (g : S →+* T)
    (hg : ∀ (s : S) (n : N), g s • n = s • n)
    (hsurj : Function.Surjective g) : Function.Bijective g :=
  RingHom.bijective_of_surjective_of_smul_eq g hg hsurj

/-- The identity hom on `S`, acting on `S` itself, is bijective. -/
public example (S : Type*) [CommRing S] [Nontrivial S] :
    Function.Bijective (RingHom.id S) :=
  RingHom.bijective_of_surjective_of_smul_eq (S := S) (T := S) (N := S)
    (RingHom.id S) (fun _ _ => rfl) Function.surjective_id

end RingHomBijectiveOfSmulTest
