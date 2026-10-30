/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.PointDerivations

@[expose] public section

example (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] (ev : A →+* k)
    (M : Type) [AddCommGroup M] [Module k M] :
    Submodule k (A →ₗ[k] M) :=
  Algebra.PointDerivations k A ev M

example (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] (ev : A →+* k)
    (M : Type) [AddCommGroup M] [Module k M] {D : A →ₗ[k] M}
    (hD : D ∈ Algebra.PointDerivations k A ev M) : D 1 = 0 :=
  Algebra.PointDerivations.apply_one hD

example (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] (ev : A →+* k)
    (M : Type) [AddCommGroup M] [Module k M] {D : A →ₗ[k] M}
    (hD : D ∈ Algebra.PointDerivations k A ev M) (c : k) : D (algebraMap k A c) = 0 :=
  Algebra.PointDerivations.apply_algebraMap hD c
