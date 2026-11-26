/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- Original implementation credit: Avocado.
module

public import MathlibExt.GroupTheory.SchreierTransversal

/-!
# Transport of Schreier decompositions by group equivalences

For a multiplicative equivalence e : G ≃* G′, restriction gives H ≃* e(H), and the image e(T)
of a right transversal T for H is a right transversal for e(H). The decomposition tg =
a(t,g)r(t,g) transports to e(t)e(g) = e(a(t,g))e(r(t,g)).

Representative scans and subgroup factor tuples commute with coordinatewise application of e.
These constructions allow independent source and target group universe levels.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Subgroup.RightTransversal

namespace SchreierEquiv

namespace Subgroup

universe u v

variable {G : Type u} {G' : Type v} [Group G] [Group G']

/-- The subgroup equivalence induced by a group equivalence.

For e : G ≃* G′ and H ≤ G, restriction of e gives the multiplicative equivalence H ≃* e(H).
The source and target group universe levels are independent. -/
noncomputable def mapMulEquivEquiv (H : Subgroup G) (e : G ≃* G') :
    H ≃* H.map (e : G →* G') :=
  H.equivMapOfInjective e.toMonoidHom e.injective

/-- Ambient values of the subgroup image equivalence.

The image of h ∈ H under the subgroup equivalence induced by e has ambient value e(h) ∈ G′. -/
theorem mapMulEquivEquiv_coe_apply (H : Subgroup G) (e : G ≃* G')
    (h : H) :
    ((SchreierEquiv.Subgroup.mapMulEquivEquiv H e h : H.map (e : G →* G')) : G') = e (h : G) :=
  rfl

/-- Subgroup transport to an identified image.

If e(H) = H′ for a subgroup H′ ≤ G′, compose H ≃* e(H) with this subgroup identification to
obtain H ≃* H′. -/
noncomputable def mapMulEquivEquivOfEq (H : Subgroup G) (e : G ≃* G')
    (H' : Subgroup G') (h : H.map (e : G →* G') = H') : H ≃* H' :=
  (SchreierEquiv.Subgroup.mapMulEquivEquiv H e).trans (MulEquiv.subgroupCongr h)

/-- Ambient values after identifying the subgroup image.

For e(H) = H′, the transported image of h ∈ H has ambient value e(h), independently of the
chosen equality identifying the subgroup image. -/
theorem mapMulEquivEquivOfEq_coe_apply (H : Subgroup G) (e : G ≃* G')
    (H' : Subgroup G') (h : H.map (e : G →* G') = H') (x : H) :
    ((SchreierEquiv.Subgroup.mapMulEquivEquivOfEq H e H' h x : H') : G') = e (x : G) := by
  subst H'
  rfl

end Subgroup

namespace Subgroup.RightTransversal

universe u v

variable {G : Type u} {G' : Type v} [Group G] [Group G'] {H : Subgroup G}

/-- The image of a transversal representative.

For a group equivalence e : G ≃* G′ and t in an H-transversal T, this is the ambient element
e(t) ∈ G′. -/
def mapMulEquivRep (e : G ≃* G') (T : H.RightTransversal)
    (t : (T : Set G)) : G' :=
  e (t : G)

/-- The image set of a right transversal.

For e : G ≃* G′, this subset of G′ is {e(t) | t ∈ T}. -/
def mapMulEquivSet (e : G ≃* G') (T : H.RightTransversal) : Set G' :=
  Set.range (mapMulEquivRep e T)

/-- An equivalence onto the representative image set.

The map t ↦ e(t) identifies T with its image subset in G′. -/
noncomputable def mapMulEquivRangeEquiv (e : G ≃* G')
    (T : H.RightTransversal) :
    (T : Set G) ≃ ↥(mapMulEquivSet e T : Set G') :=
  Equiv.ofInjective (mapMulEquivRep e T)
    (e.injective.comp Subtype.val_injective)

/-- Values of the representative image-set equivalence.

The representative-image equivalence sends t ∈ T to an element with ambient value e(t) ∈ G′. -/
theorem mapMulEquivRangeEquiv_coe_apply (e : G ≃* G')
    (T : H.RightTransversal)
    (t : (T : Set G)) :
    ((mapMulEquivRangeEquiv e T t :
      ↥(mapMulEquivSet e T : Set G')) : G') = e (t : G) :=
  rfl

/-- A right transversal transported by a group equivalence.

The image e(T) is a right transversal for the subgroup image e(H) in G′. Unique subgroup-
representative decomposition is transported along e. -/
noncomputable abbrev mapMulEquiv (e : G ≃* G') (T : H.RightTransversal) :
    (H.map (e : G →* G')).RightTransversal := by
  refine ⟨mapMulEquivSet e T, ?_⟩
  change Function.Bijective
    (fun p : (H.map (e : G →* G')) × ↥(mapMulEquivSet e T : Set G') =>
      (p.1 : G') * (p.2 : G'))
  let d : (H.map (e : G →* G')) × ↥(mapMulEquivSet e T : Set G') ≃
      H × ↥(T : Set G) :=
    Equiv.prodCongr (SchreierEquiv.Subgroup.mapMulEquivEquiv H e).symm.toEquiv
      (mapMulEquivRangeEquiv e T).symm
  have hb : Function.Bijective
      (e.toEquiv ∘ (fun p : H × ↥(T : Set G) =>
        (p.1 : G) * (p.2 : G)) ∘ d) :=
    e.bijective.comp (T.2.comp d.bijective)
  have hfun :
      (fun p : (H.map (e : G →* G')) × ↥(mapMulEquivSet e T : Set G') =>
        (p.1 : G') * (p.2 : G')) =
      (e.toEquiv ∘ (fun p : H × ↥(T : Set G) =>
        (p.1 : G) * (p.2 : G)) ∘ d) := by
    funext p
    change (p.1 : G') * (p.2 : G') =
      e (((d p).1 : G) * ((d p).2 : G))
    rw [map_mul]
    congr 1
    · change (p.1 : G') =
        e (((SchreierEquiv.Subgroup.mapMulEquivEquiv H e).symm p.1 : H) : G)
      exact (congrArg Subtype.val
        ((SchreierEquiv.Subgroup.mapMulEquivEquiv H e).apply_symm_apply p.1)).symm
    · change (p.2 : G') = e
        (((mapMulEquivRangeEquiv e T).symm p.2 : (T : Set G)) : G)
      exact (congrArg Subtype.val
        ((mapMulEquivRangeEquiv e T).apply_symm_apply p.2)).symm
  rw [hfun]
  exact hb

/-- The equivalence between a transversal and its transport.

For e : G ≃* G′, this equivalence sends t ∈ T to e(t) in the transported e(H)-transversal
e(T). -/
noncomputable def mapMulEquivRepEquiv (e : G ≃* G')
    (T : H.RightTransversal) :
    (T : Set G) ≃ ((mapMulEquiv e T : Set G')) :=
  mapMulEquivRangeEquiv e T

/-- Values of the transported-transversal equivalence.

The element corresponding to t in the transported transversal has ambient value e(t). -/
theorem mapMulEquivRepEquiv_coe_apply (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) :
    ((mapMulEquivRepEquiv e T t : ((mapMulEquiv e T : Set G'))) : G') =
      e (t : G) :=
  rfl

/-- Schreier decompositions commute with group equivalences.

For tg = a(t,g)r(t,g), the decomposition of e(t)e(g) in the transported transversal has factor
e(a(t,g)) in e(H) and representative e(r(t,g)) in e(T). -/
theorem mapMulEquiv_schreierDecomposition (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) (g : G) :
    ((mapMulEquiv e T).schreierFactor (mapMulEquivRepEquiv e T t) (e g),
        (mapMulEquiv e T).schreierRep
          (mapMulEquivRepEquiv e T t) (e g)) =
      (SchreierEquiv.Subgroup.mapMulEquivEquiv H e (T.schreierFactor t g),
        mapMulEquivRepEquiv e T (T.schreierRep t g)) := by
  apply (mapMulEquiv e T).2.1
  calc
    ((mapMulEquiv e T).schreierFactor
          (mapMulEquivRepEquiv e T t) (e g) : G') *
        ((mapMulEquiv e T).schreierRep
          (mapMulEquivRepEquiv e T t) (e g) : G') =
      (mapMulEquivRepEquiv e T t : G') * e g :=
        (mapMulEquiv e T).schreierFactor_mul_schreierRep
          (mapMulEquivRepEquiv e T t) (e g)
    _ = e ((t : G) * g) := by rw [mapMulEquivRepEquiv_coe_apply, map_mul]
    _ = e ((T.schreierFactor t g : G) *
        (T.schreierRep t g : G)) := by
      rw [T.schreierFactor_mul_schreierRep]
    _ = (SchreierEquiv.Subgroup.mapMulEquivEquiv H e (T.schreierFactor t g) : G') *
        (mapMulEquivRepEquiv e T (T.schreierRep t g) : G') := by
      rw [map_mul, mapMulEquivRepEquiv_coe_apply]
      rfl

/-- Transport of Schreier representatives.

The representative of e(t)e(g) in e(T) is the image under e of the representative of tg in T. -/
theorem mapMulEquiv_schreierRep (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) (g : G) :
    (mapMulEquiv e T).schreierRep (mapMulEquivRepEquiv e T t) (e g) =
      mapMulEquivRepEquiv e T (T.schreierRep t g) :=
  congrArg Prod.snd (mapMulEquiv_schreierDecomposition e T t g)

/-- Transport of Schreier subgroup factors.

The subgroup factor of e(t)e(g) in e(H) is the image under the induced subgroup equivalence of
the factor of tg in H. -/
theorem mapMulEquiv_schreierFactor (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) (g : G) :
    (mapMulEquiv e T).schreierFactor (mapMulEquivRepEquiv e T t) (e g) =
      SchreierEquiv.Subgroup.mapMulEquivEquiv H e (T.schreierFactor t g) :=
  congrArg Prod.fst (mapMulEquiv_schreierDecomposition e T t g)

end Subgroup.RightTransversal

namespace Subgroup.RightTransversal

universe u v

variable {G : Type u} {G' : Type v} [Group G] [Group G'] {H : Subgroup G}

/-- Transport of finite representative scans.

Applying e to the starting representative and every coordinate of g : Fin n → G transports
each step of the representative scan to its image in e(T). -/
theorem mapMulEquiv_schreierRepScan {n : ℕ}
    (e : G ≃* G') (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) (i : Fin (n + 1)) :
    (SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv e T).schreierRepScan
        (SchreierEquiv.Subgroup.RightTransversal.mapMulEquivRepEquiv e T t) (fun j ↦ e (g j)) i =
      SchreierEquiv.Subgroup.RightTransversal.mapMulEquivRepEquiv e T (T.schreierRepScan t g i)
        := by
  induction i using Fin.induction with
  | zero =>
      simp only [schreierRepScan_get_zero]
  | succ i ih =>
      rw [schreierRepScan_get_succ, ih,
        SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv_schreierRep e T,
        schreierRepScan_get_succ]

/-- Transport of finite subgroup factor tuples.

For a tuple g : Fin n → G, the factor tuple of its coordinatewise image under e is the
coordinatewise image of the original factor tuple under H ≃* e(H). -/
theorem mapMulEquiv_schreierFactorTuple {n : ℕ}
    (e : G ≃* G') (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) :
    (SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv e T).schreierFactorTuple
        (SchreierEquiv.Subgroup.RightTransversal.mapMulEquivRepEquiv e T t) (fun j ↦ e (g j)) =
      fun i ↦ SchreierEquiv.Subgroup.mapMulEquivEquiv H e (T.schreierFactorTuple t g i) := by
  funext i
  unfold schreierFactorTuple
  rw [SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv_schreierRepScan e T]
  exact SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv_schreierFactor e T
    (T.schreierRepScan t g i.castSucc) (g i)

end Subgroup.RightTransversal


end SchreierEquiv

/-!
# Subgroup and transversal transport in a common universe

When G and G′ lie in the same universe, the subgroup-image equivalence, transported
transversal, representative decomposition, finite scan and factor-tuple formulas specialize to
the same maps h ↦ e(h) and t ↦ e(t).
-/

namespace Subgroup

universe u

variable {G G' : Type u} [Group G] [Group G']

/-- Subgroup image equivalence in a common universe.

For e : G ≃* G′ and H ≤ G, restriction of e gives the multiplicative equivalence H ≃* e(H).
The two groups here lie in the same stated universe. -/
noncomputable abbrev mapMulEquivEquiv (H : Subgroup G) (e : G ≃* G') :
    H ≃* H.map e.toMonoidHom :=
  SchreierEquiv.Subgroup.mapMulEquivEquiv H e

/-- Subgroup image values in a common universe.

The image of h ∈ H under the subgroup equivalence induced by e has ambient value e(h) ∈ G′.
The two groups here lie in the same stated universe. -/
@[simp]
theorem mapMulEquivEquiv_coe_apply (H : Subgroup G) (e : G ≃* G')
    (h : H) :
    ((SchreierEquiv.Subgroup.mapMulEquivEquiv H e h : H.map (e : G →* G')) : G') = e (h : G) :=
  SchreierEquiv.Subgroup.mapMulEquivEquiv_coe_apply H e h

/-- Subgroup transport to an equal image in a common universe.

If e(H) = H′ for a subgroup H′ ≤ G′, compose H ≃* e(H) with this subgroup identification to
obtain H ≃* H′. The two groups here lie in the same stated universe. -/
noncomputable abbrev mapMulEquivEquivOfEq (H : Subgroup G) (e : G ≃* G')
    (H' : Subgroup G') (h : H.map e.toMonoidHom = H') : H ≃* H' :=
  SchreierEquiv.Subgroup.mapMulEquivEquivOfEq H e H' h

/-- Values of identified subgroup transport in a common universe.

For e(H) = H′, the transported image of h ∈ H has ambient value e(h), independently of the
chosen equality identifying the subgroup image. The two groups here lie in the same stated
universe. -/
@[simp]
theorem mapMulEquivEquivOfEq_coe_apply (H : Subgroup G) (e : G ≃* G')
    (H' : Subgroup G') (h : H.map e.toMonoidHom = H') (x : H) :
    ((H.mapMulEquivEquivOfEq e H' h x : H') : G') = e (x : G) :=
  SchreierEquiv.Subgroup.mapMulEquivEquivOfEq_coe_apply H e H' h x

end Subgroup

namespace Subgroup.RightTransversal

universe u

variable {G G' : Type u} [Group G] [Group G'] {H : Subgroup G}

/-- Image of a representative in a common universe.

For a group equivalence e : G ≃* G′ and t in an H-transversal T, this is the ambient element
e(t) ∈ G′. The two groups here lie in the same stated universe. -/
abbrev mapMulEquivRep (e : G ≃* G') (T : H.RightTransversal)
    (t : (T : Set G)) : G' :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquivRep e T t

/-- Image transversal set in a common universe.

For e : G ≃* G′, this subset of G′ is {e(t) | t ∈ T}. The two groups here lie in the same
stated universe. -/
abbrev mapMulEquivSet (e : G ≃* G') (T : H.RightTransversal) : Set G' :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquivSet e T

/-- Representative image equivalence in a common universe.

The map t ↦ e(t) identifies T with its image subset in G′. The two groups here lie in the same
stated universe. -/
noncomputable abbrev mapMulEquivRangeEquiv (e : G ≃* G')
    (T : H.RightTransversal) :
    (T : Set G) ≃ ↥(mapMulEquivSet e T : Set G') :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquivRangeEquiv e T

/-- Values of the representative image equivalence in a common universe.

The representative-image equivalence sends t ∈ T to an element with ambient value e(t) ∈ G′.
The two groups here lie in the same stated universe. -/
@[simp]
theorem mapMulEquivRangeEquiv_coe_apply (e : G ≃* G')
    (T : H.RightTransversal)
    (t : (T : Set G)) :
    ((mapMulEquivRangeEquiv e T t :
      ↥(mapMulEquivSet e T : Set G')) : G') = e (t : G) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquivRangeEquiv_coe_apply e T t

/-- Transported right transversal in a common universe.

The image e(T) is a right transversal for the subgroup image e(H) in G′. Unique subgroup-
representative decomposition is transported along e. The two groups here lie in the same
stated universe. -/
noncomputable abbrev mapMulEquiv (e : G ≃* G') (T : H.RightTransversal) :
    (H.map e.toMonoidHom).RightTransversal :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv e T

/-- Transversal transport equivalence in a common universe.

For e : G ≃* G′, this equivalence sends t ∈ T to e(t) in the transported e(H)-transversal
e(T). The two groups here lie in the same stated universe. -/
noncomputable abbrev mapMulEquivRepEquiv (e : G ≃* G')
    (T : H.RightTransversal) :
    (T : Set G) ≃ ((mapMulEquiv e T : Set G')) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquivRepEquiv e T

/-- Values of transversal transport in a common universe.

The element corresponding to t in the transported transversal has ambient value e(t). The two
groups here lie in the same stated universe. -/
@[simp]
theorem mapMulEquivRepEquiv_coe_apply (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) :
    ((mapMulEquivRepEquiv e T t : ((mapMulEquiv e T : Set G'))) : G') =
      e (t : G) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquivRepEquiv_coe_apply e T t

/-- Schreier decomposition transport in a common universe.

For tg = a(t,g)r(t,g), the decomposition of e(t)e(g) in the transported transversal has factor
e(a(t,g)) in e(H) and representative e(r(t,g)) in e(T). The two groups here lie in the same
stated universe. -/
theorem mapMulEquiv_schreierDecomposition (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) (g : G) :
    ((mapMulEquiv e T).schreierFactor (mapMulEquivRepEquiv e T t) (e g),
        (mapMulEquiv e T).schreierRep
          (mapMulEquivRepEquiv e T t) (e g)) =
      (H.mapMulEquivEquiv e (T.schreierFactor t g),
        mapMulEquivRepEquiv e T (T.schreierRep t g)) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv_schreierDecomposition e T t g

/-- Schreier representative transport in a common universe.

The representative of e(t)e(g) in e(T) is the image under e of the representative of tg in T.
The two groups here lie in the same stated universe. -/
theorem mapMulEquiv_schreierRep (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) (g : G) :
    (mapMulEquiv e T).schreierRep (mapMulEquivRepEquiv e T t) (e g) =
      mapMulEquivRepEquiv e T (T.schreierRep t g) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv_schreierRep e T t g

/-- Schreier factor transport in a common universe.

The subgroup factor of e(t)e(g) in e(H) is the image under the induced subgroup equivalence of
the factor of tg in H. The two groups here lie in the same stated universe. -/
theorem mapMulEquiv_schreierFactor (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) (g : G) :
    (mapMulEquiv e T).schreierFactor (mapMulEquivRepEquiv e T t) (e g) =
      H.mapMulEquivEquiv e (T.schreierFactor t g) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv_schreierFactor e T t g

end Subgroup.RightTransversal

namespace Subgroup.RightTransversal

universe u

variable {G G' : Type u} [Group G] [Group G'] {H : Subgroup G}

/-- Representative scan transport in a common universe.

Applying e to the starting representative and every coordinate of g : Fin n → G transports
each step of the representative scan to its image in e(T). The two groups here lie in the same
stated universe. -/
theorem mapMulEquiv_schreierRepScan {n : ℕ}
    (e : G ≃* G') (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) (i : Fin (n + 1)) :
    (T.mapMulEquiv e).schreierRepScan
        (T.mapMulEquivRepEquiv e t) (fun j ↦ e (g j)) i =
      T.mapMulEquivRepEquiv e (T.schreierRepScan t g i) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv_schreierRepScan e T t g i

/-- Factor tuple transport in a common universe.

For a tuple g : Fin n → G, the factor tuple of its coordinatewise image under e is the
coordinatewise image of the original factor tuple under H ≃* e(H). The two groups here lie in
the same stated universe. -/
theorem mapMulEquiv_schreierFactorTuple {n : ℕ}
    (e : G ≃* G') (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) :
    (T.mapMulEquiv e).schreierFactorTuple
        (T.mapMulEquivRepEquiv e t) (fun j ↦ e (g j)) =
      fun i ↦ H.mapMulEquivEquiv e (T.schreierFactorTuple t g i) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv_schreierFactorTuple e T t g

end Subgroup.RightTransversal
