/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- SOURCE-ONLY PROPOSAL. Native verification is UNEXECUTED.
module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentPushout
public import MathlibExt.Algebra.Category.CommAlgCat.ScalarExtensionAdjunction
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Tensor-pushout adjunction for commutative algebras

Let `k : Type u` and `K : Type w` be commutative rings with `Algebra k K`. On algebra carriers
of universe `max u v w`, the tensor-pushout functor `P ↦ K ⊗_k P` is left adjoint to
restriction along `algebraMap k K`.

Its Hom correspondence is `Hom_K(K ⊗_k P,Q) ≅ Hom_k(P,Res Q)`. Precomposition in `P` and
postcomposition in `Q` satisfy the adjunction naturality equations.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace CommAlgCat.CotangentPushout

variable (k : Type u) (K : Type w) [CommRing k] [CommRing K] [Algebra k K]

/-- For commutative rings `k : Type u`, `K : Type w` with `Algebra k K`, `restrictionFunctor k K :
CommAlgCat.{max u v w} K → CommAlgCat.{max u v w} k` restricts scalars along `algebraMap k K`.
Each algebra retains its carrier and underlying ring. -/
abbrev restrictionFunctor :
    CommAlgCat.{max u v w} K ⥤ CommAlgCat.{max u v w} k :=
  CommAlgCat.restrictScalars (algebraMap k K)

/-- Let `k,K` be commutative rings with `Algebra k K`. At carrier height `max u v w`,
`algebraFunctor k K ⊣ restrictionFunctor k K`. This is the scalar-extension adjunction
specialized to the structural map `algebraMap k K`. -/
abbrev adjunction : algebraFunctor.{u, v, w} k K ⊣ restrictionFunctor.{u, v, w} k K :=
  (CommAlgCat.extendRestrictScalarsAdj.{u, w, v} (algebraMap k K)).ofNatIsoLeft
    (eqToIso (CommAlgCat.extendScalars_algebraMap.{u, w, v} (R := k) (S := K)))

/-- For commutative `k`-algebra `K`, a `k`-algebra `P`, and a `K`-algebra `Q` at height `max u v
w`, `homEquiv k K P Q` identifies `Hom_K(K ⊗_k P,Q)` with `Hom_k(P,Res Q)`. It is the Hom
equivalence of the tensor-pushout/restriction adjunction. -/
abbrev homEquiv (P : CommAlgCat.{max u v w} k) (Q : CommAlgCat.{max u v w} K) :
    ((algebraFunctor.{u, v, w} k K).obj P ⟶ Q) ≃ (P ⟶ (restrictionFunctor.{u, v, w} k K).obj Q) :=
  (adjunction.{u, v, w} k K).homEquiv P Q

/-- Let `k,K` be commutative rings with `Algebra k K`, `f : P' → P` a `k`-algebra morphism, and `g
: P → Res Q` for a `K`-algebra `Q`. If `α` is the tensor-pushout Hom equivalence and `E(P)=K
⊗_k P`, then `α_{P',Q}⁻¹(f ≫ g) = E(f) ≫ α_{P,Q}⁻¹(g)`. -/
theorem homEquiv_left_symm
    {P P' : CommAlgCat.{max u v w} k} {Q : CommAlgCat.{max u v w} K}
    (f : P' ⟶ P) (g : P ⟶ (restrictionFunctor.{u, v, w} k K).obj Q) :
    (homEquiv.{u, v, w} k K P' Q).symm (f ≫ g) =
      (algebraFunctor.{u, v, w} k K).map f ≫ (homEquiv.{u, v, w} k K P Q).symm g :=
  (adjunction.{u, v, w} k K).homEquiv_naturality_left_symm f g

/-- Let `k,K` be commutative rings with `Algebra k K`, `f : K ⊗_k P → Q` a `K`-algebra morphism,
and `g : Q → Q'`. For the adjunction Hom equivalence `α`, `α_{P,Q'}(f ≫ g) = α_{P,Q}(f) ≫
restrictionFunctor(g)`. -/
theorem homEquiv_right
    {P : CommAlgCat.{max u v w} k} {Q Q' : CommAlgCat.{max u v w} K}
    (f : (algebraFunctor.{u, v, w} k K).obj P ⟶ Q) (g : Q ⟶ Q') :
    homEquiv.{u, v, w} k K P Q' (f ≫ g) =
      homEquiv.{u, v, w} k K P Q f ≫ (restrictionFunctor.{u, v, w} k K).map g :=
  (adjunction.{u, v, w} k K).homEquiv_naturality_right f g

instance algebraFunctor_isLeftAdjoint : (algebraFunctor.{u, v, w} k K).IsLeftAdjoint :=
  (adjunction.{u, v, w} k K).isLeftAdjoint

end CommAlgCat.CotangentPushout

end
