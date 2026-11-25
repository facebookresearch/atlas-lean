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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.AsymptoticAlgebraMap
public import MathlibExt.Analysis.CStarAlgebra.Pullback

import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# The asymptotic-algebra comparison for a literal pullback

Applying the literal asymptotic-algebra functor to the two coordinate maps
gives the canonical comparison from the asymptotic algebra of a pullback to
the pullback of the two induced coefficient maps.

The comparison is injective. If the right leg of the cospan has a
star-homomorphic section, it is surjective and therefore gives a
star-algebra equivalence. The file stops before finite iteration, matching
paths, gluing, endpoint laws, or an n-homotopy relation.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped BoundedContinuousFunction CStarAlgebra

noncomputable section

namespace AsymptoticAlgebra

universe uA uB uC

attribute [local instance] cStarAlgebra

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [NonUnitalCStarAlgebra C]

/-- The canonical map from the asymptotic algebra of a literal pullback to
the pullback of the two induced coefficient maps. -/
def pullbackComparison
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) :
    AsymptoticAlgebra (NonUnitalCStarPullback.Pullback f g) →⋆ₙₐ[ℂ]
      NonUnitalCStarPullback.Pullback (map f) (map g) := by
  have hcompat :
      (map f).comp
          (map (NonUnitalCStarPullback.fstHom f g)) =
        (map g).comp
          (map (NonUnitalCStarPullback.sndHom f g)) := by
    calc
      (map f).comp
          (map (NonUnitalCStarPullback.fstHom f g)) =
        map (f.comp (NonUnitalCStarPullback.fstHom f g)) :=
          (map_comp (NonUnitalCStarPullback.fstHom f g) f).symm
      _ = map (g.comp (NonUnitalCStarPullback.sndHom f g)) :=
        congrArg
          (fun h : NonUnitalCStarPullback.Pullback f g →⋆ₙₐ[ℂ] C =>
            map h)
          (NonUnitalCStarPullback.condition_hom f g)
      _ = (map g).comp
          (map (NonUnitalCStarPullback.sndHom f g)) :=
        map_comp (NonUnitalCStarPullback.sndHom f g) g
  exact NonUnitalCStarPullback.lift (map f) (map g)
    (map (NonUnitalCStarPullback.fstHom f g))
    (map (NonUnitalCStarPullback.sndHom f g)) hcompat

/-- The first coordinate of the comparison is the induced first-coordinate
coefficient map. -/
theorem fstHom_comp_pullbackComparison
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) :
    (NonUnitalCStarPullback.fstHom (map f) (map g)).comp
        (pullbackComparison f g) =
      map (NonUnitalCStarPullback.fstHom f g) := by
  apply NonUnitalStarAlgHom.ext
  intro q
  rfl

/-- The second coordinate of the comparison is the induced second-coordinate
coefficient map. -/
theorem sndHom_comp_pullbackComparison
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) :
    (NonUnitalCStarPullback.sndHom (map f) (map g)).comp
        (pullbackComparison f g) =
      map (NonUnitalCStarPullback.sndHom f g) := by
  apply NonUnitalStarAlgHom.ext
  intro q
  rfl

/-- The canonical comparison is injective.  A quotient class whose two
coordinate classes vanish has a representative whose two coordinate
functions tend to zero, hence the pullback-valued representative itself
tends to zero. -/
theorem pullbackComparison_injective
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) :
    Function.Injective (pullbackComparison f g) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hcomp : pullbackComparison f g (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨p, hp⟩ :=
    quotientMap_surjective
      (NonUnitalCStarPullback.Pullback f g) (x - y)
  have hcompP :
      pullbackComparison f g
          (quotientMap (NonUnitalCStarPullback.Pullback f g) p) = 0 := by
    rw [hp]
    exact hcomp
  have hfstQ :
      map (NonUnitalCStarPullback.fstHom f g)
          (quotientMap (NonUnitalCStarPullback.Pullback f g) p) = 0 := by
    calc
      map (NonUnitalCStarPullback.fstHom f g)
          (quotientMap (NonUnitalCStarPullback.Pullback f g) p) =
        NonUnitalCStarPullback.fstHom (map f) (map g)
          (pullbackComparison f g
            (quotientMap (NonUnitalCStarPullback.Pullback f g) p)) :=
        (DFunLike.congr_fun (fstHom_comp_pullbackComparison f g) _).symm
      _ = NonUnitalCStarPullback.fstHom (map f) (map g) 0 :=
        congrArg (NonUnitalCStarPullback.fstHom (map f) (map g)) hcompP
      _ = 0 := _root_.map_zero _
  have hsndQ :
      map (NonUnitalCStarPullback.sndHom f g)
          (quotientMap (NonUnitalCStarPullback.Pullback f g) p) = 0 := by
    calc
      map (NonUnitalCStarPullback.sndHom f g)
          (quotientMap (NonUnitalCStarPullback.Pullback f g) p) =
        NonUnitalCStarPullback.sndHom (map f) (map g)
          (pullbackComparison f g
            (quotientMap (NonUnitalCStarPullback.Pullback f g) p)) :=
        (DFunLike.congr_fun (sndHom_comp_pullbackComparison f g) _).symm
      _ = NonUnitalCStarPullback.sndHom (map f) (map g) 0 :=
        congrArg (NonUnitalCStarPullback.sndHom (map f) (map g)) hcompP
      _ = 0 := _root_.map_zero _
  have hfstClass :
      quotientMap A
          (BoundedContinuousFunction.compNonUnitalStarAlgHom
            (NonUnitalCStarPullback.fstHom f g) p) = 0 := by
    simpa only [map_quotientMap] using hfstQ
  have hsndClass :
      quotientMap B
          (BoundedContinuousFunction.compNonUnitalStarAlgHom
            (NonUnitalCStarPullback.sndHom f g) p) = 0 := by
    simpa only [map_quotientMap] using hsndQ
  have hfst :
      Tendsto (fun t : AsymptoticTime =>
          NonUnitalCStarPullback.fst f g (p t))
        atTop (nhds (0 : A)) := by
    have haction :
        (BoundedContinuousFunction.compNonUnitalStarAlgHom
          (NonUnitalCStarPullback.fstHom f g) p : AsymptoticTime → A) =
        fun t => NonUnitalCStarPullback.fst f g (p t) := by
      funext t
      rw [BoundedContinuousFunction.compNonUnitalStarAlgHom_apply,
        NonUnitalCStarPullback.fstHom_apply]
    rw [← haction]
    exact (quotientMap_eq_zero_iff _).1 hfstClass
  have hsnd :
      Tendsto (fun t : AsymptoticTime =>
          NonUnitalCStarPullback.snd f g (p t))
        atTop (nhds (0 : B)) := by
    have haction :
        (BoundedContinuousFunction.compNonUnitalStarAlgHom
          (NonUnitalCStarPullback.sndHom f g) p : AsymptoticTime → B) =
        fun t => NonUnitalCStarPullback.snd f g (p t) := by
      funext t
      rw [BoundedContinuousFunction.compNonUnitalStarAlgHom_apply,
        NonUnitalCStarPullback.sndHom_apply]
    rw [← haction]
    exact (quotientMap_eq_zero_iff _).1 hsndClass
  have hpzero :
      Tendsto (fun t : AsymptoticTime => p t) atTop
        (nhds (0 : NonUnitalCStarPullback.Pullback f g)) := by
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun t : AsymptoticTime =>
        ((p t : NonUnitalCStarPullback.Pullback f g) : A × B))
      atTop
      (nhds (((0 : NonUnitalCStarPullback.Pullback f g) : A × B)))
    have hpair := hfst.prodMk_nhds hsnd
    change Tendsto (fun t : AsymptoticTime => ((p t).1.1, (p t).1.2))
      atTop (nhds ((0 : A), (0 : B))) at hpair
    convert hpair using 1
  calc
    x - y = quotientMap (NonUnitalCStarPullback.Pullback f g) p := hp.symm
    _ = 0 := (quotientMap_eq_zero_iff p).2 hpzero

/-- The canonical comparison is surjective when the right leg of the
defining cospan has a star-homomorphic section. -/
theorem pullbackComparison_surjective_of_rightInverse
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (s : C →⋆ₙₐ[ℂ] B)
    (hs : g.comp s = NonUnitalStarAlgHom.id ℂ C) :
    Function.Surjective (pullbackComparison f g) := by
  intro q
  obtain ⟨x, hx⟩ :=
    quotientMap_surjective A
      (NonUnitalCStarPullback.fstHom (map f) (map g) q)
  obtain ⟨y, hy⟩ :=
    quotientMap_surjective B
      (NonUnitalCStarPullback.sndHom (map f) (map g) q)
  have hcompatQ :
      map f (quotientMap A x) = map g (quotientMap B y) := by
    calc
      map f (quotientMap A x) =
          map f (NonUnitalCStarPullback.fstHom (map f) (map g) q) :=
        congrArg (map f) hx
      _ = map g (NonUnitalCStarPullback.sndHom (map f) (map g) q) :=
        NonUnitalCStarPullback.condition (map f) (map g) q
      _ = map g (quotientMap B y) :=
        congrArg (map g) hy.symm
  let delta : AsymptoticTime →ᵇ C :=
    BoundedContinuousFunction.compNonUnitalStarAlgHom f x -
      BoundedContinuousFunction.compNonUnitalStarAlgHom g y
  have hdeltaQ : quotientMap C delta = 0 := by
    dsimp only [delta]
    calc
      quotientMap C
          (BoundedContinuousFunction.compNonUnitalStarAlgHom f x -
            BoundedContinuousFunction.compNonUnitalStarAlgHom g y) =
        quotientMap C
            (BoundedContinuousFunction.compNonUnitalStarAlgHom f x) -
          quotientMap C
            (BoundedContinuousFunction.compNonUnitalStarAlgHom g y) :=
        map_sub _ _ _
      _ = map f (quotientMap A x) - map g (quotientMap B y) := by
        rw [← map_quotientMap f x, ← map_quotientMap g y]
      _ = 0 := by rw [hcompatQ, sub_self]
  have hdelta :
      Tendsto (fun t : AsymptoticTime => delta t) atTop (nhds (0 : C)) :=
    (quotientMap_eq_zero_iff delta).1 hdeltaQ
  let correction : AsymptoticTime →ᵇ B :=
    BoundedContinuousFunction.compNonUnitalStarAlgHom s delta
  have hcorrection :
      Tendsto (fun t : AsymptoticTime => correction t)
        atTop (nhds (0 : B)) := by
    have hS : Continuous (s : C → B) := map_continuous s
    have hs0 := (hS.tendsto (0 : C)).comp hdelta
    simpa only [correction,
      BoundedContinuousFunction.compNonUnitalStarAlgHom_apply,
      Function.comp_def, _root_.map_zero] using hs0
  have hcorrectionQ : quotientMap B correction = 0 :=
    (quotientMap_eq_zero_iff correction).2 hcorrection
  let y' : AsymptoticTime →ᵇ B := y + correction
  have hy' :
      quotientMap B y' =
        NonUnitalCStarPullback.sndHom (map f) (map g) q := by
    dsimp only [y']
    rw [map_add, hcorrectionQ, add_zero, hy]
  have hpoint (t : AsymptoticTime) : f (x t) = g (y' t) := by
    have hsval :
        g (s (f (x t) - g (y t))) = f (x t) - g (y t) := by
      have h := DFunLike.congr_fun hs (f (x t) - g (y t))
      change g (s (f (x t) - g (y t))) = f (x t) - g (y t) at h
      exact h
    dsimp only [y', correction, delta]
    rw [BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.compNonUnitalStarAlgHom_apply,
      BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.compNonUnitalStarAlgHom_apply,
      BoundedContinuousFunction.compNonUnitalStarAlgHom_apply,
      map_add, hsval, add_comm, sub_add_cancel]
  let pair : AsymptoticTime →ᵇ (A × B) :=
    { toFun := fun t => (x t, y' t)
      continuous_toFun := x.continuous.prodMk y'.continuous
      map_bounded' := by
        obtain ⟨Kx, hKx⟩ := x.bounded
        obtain ⟨Ky, hKy⟩ := y'.bounded
        refine ⟨max Kx Ky, fun t u => ?_⟩
        rw [Prod.dist_eq]
        exact max_le_max (hKx t u) (hKy t u) }
  let p : AsymptoticTime →ᵇ
      NonUnitalCStarPullback.Pullback f g :=
    BoundedContinuousFunction.codRestrict
      (NonUnitalCStarPullback.Pullback f g) pair fun t =>
        (NonUnitalCStarPullback.mem_pullback f g _).2 (hpoint t)
  have hpFst :
      BoundedContinuousFunction.compNonUnitalStarAlgHom
          (NonUnitalCStarPullback.fstHom f g) p = x := by
    apply BoundedContinuousFunction.ext
    intro t
    rw [BoundedContinuousFunction.compNonUnitalStarAlgHom_apply,
      NonUnitalCStarPullback.fstHom_apply]
    rfl
  have hpSnd :
      BoundedContinuousFunction.compNonUnitalStarAlgHom
          (NonUnitalCStarPullback.sndHom f g) p = y' := by
    apply BoundedContinuousFunction.ext
    intro t
    rw [BoundedContinuousFunction.compNonUnitalStarAlgHom_apply,
      NonUnitalCStarPullback.sndHom_apply]
    rfl
  refine ⟨quotientMap (NonUnitalCStarPullback.Pullback f g) p, ?_⟩
  apply NonUnitalCStarPullback.ext (map f) (map g)
  · calc
      NonUnitalCStarPullback.fstHom (map f) (map g)
          (pullbackComparison f g
            (quotientMap (NonUnitalCStarPullback.Pullback f g) p)) =
        map (NonUnitalCStarPullback.fstHom f g)
          (quotientMap (NonUnitalCStarPullback.Pullback f g) p) :=
        DFunLike.congr_fun (fstHom_comp_pullbackComparison f g) _
      _ = quotientMap A
          (BoundedContinuousFunction.compNonUnitalStarAlgHom
            (NonUnitalCStarPullback.fstHom f g) p) :=
        map_quotientMap _ _
      _ = quotientMap A x := congrArg (quotientMap A) hpFst
      _ = NonUnitalCStarPullback.fstHom (map f) (map g) q := hx
  · calc
      NonUnitalCStarPullback.sndHom (map f) (map g)
          (pullbackComparison f g
            (quotientMap (NonUnitalCStarPullback.Pullback f g) p)) =
        map (NonUnitalCStarPullback.sndHom f g)
          (quotientMap (NonUnitalCStarPullback.Pullback f g) p) :=
        DFunLike.congr_fun (sndHom_comp_pullbackComparison f g) _
      _ = quotientMap B
          (BoundedContinuousFunction.compNonUnitalStarAlgHom
            (NonUnitalCStarPullback.sndHom f g) p) :=
        map_quotientMap _ _
      _ = quotientMap B y' := congrArg (quotientMap B) hpSnd
      _ = NonUnitalCStarPullback.sndHom (map f) (map g) q := hy'

/-- The canonical comparison as a star-algebra equivalence when the right
leg of the cospan has a star-homomorphic section. -/
noncomputable def splitPullbackEquiv
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (s : C →⋆ₙₐ[ℂ] B)
    (hs : g.comp s = NonUnitalStarAlgHom.id ℂ C) :
    AsymptoticAlgebra (NonUnitalCStarPullback.Pullback f g) ≃⋆ₐ[ℂ]
      NonUnitalCStarPullback.Pullback (map f) (map g) :=
  StarAlgEquiv.ofBijective (pullbackComparison f g)
    ⟨pullbackComparison_injective f g,
      pullbackComparison_surjective_of_rightInverse f g s hs⟩

/-- The forward homomorphism of the split-pullback equivalence is the
canonical comparison. -/
theorem splitPullbackEquiv_toNonUnitalStarAlgHom
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (s : C →⋆ₙₐ[ℂ] B)
    (hs : g.comp s = NonUnitalStarAlgHom.id ℂ C) :
    (splitPullbackEquiv f g s hs).toNonUnitalStarAlgHom =
      pullbackComparison f g := by
  apply NonUnitalStarAlgHom.ext
  intro q
  rfl

/-- The first projection of the split-pullback equivalence is the induced
first-coordinate coefficient map. -/
theorem fstHom_comp_splitPullbackEquiv
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (s : C →⋆ₙₐ[ℂ] B)
    (hs : g.comp s = NonUnitalStarAlgHom.id ℂ C) :
    (NonUnitalCStarPullback.fstHom (map f) (map g)).comp
        (splitPullbackEquiv f g s hs).toNonUnitalStarAlgHom =
      map (NonUnitalCStarPullback.fstHom f g) := by
  rw [splitPullbackEquiv_toNonUnitalStarAlgHom]
  exact fstHom_comp_pullbackComparison f g

/-- The second projection of the split-pullback equivalence is the induced
second-coordinate coefficient map. -/
theorem sndHom_comp_splitPullbackEquiv
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (s : C →⋆ₙₐ[ℂ] B)
    (hs : g.comp s = NonUnitalStarAlgHom.id ℂ C) :
    (NonUnitalCStarPullback.sndHom (map f) (map g)).comp
        (splitPullbackEquiv f g s hs).toNonUnitalStarAlgHom =
      map (NonUnitalCStarPullback.sndHom f g) := by
  rw [splitPullbackEquiv_toNonUnitalStarAlgHom]
  exact sndHom_comp_pullbackComparison f g


end AsymptoticAlgebra
