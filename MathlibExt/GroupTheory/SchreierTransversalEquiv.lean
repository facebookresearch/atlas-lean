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
# Pure Schreier transversal transport by group equivalences

The existing subgroup-image and right-transversal API is housed here without
representation or cohomology dependencies. Independent source and target
group universes are retained. Subgroup image/comap compatibility uses the
stock `Subgroup.map_equiv_eq_comap_symm'` theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Subgroup.RightTransversal

namespace SchreierEquiv

namespace Subgroup

universe u v

variable {G : Type u} {G' : Type v} [Group G] [Group G']

/-- The canonical equivalence from a subgroup to its image under a
multiplicative equivalence, with the image written using the underlying
monoid homomorphism. -/
noncomputable def mapMulEquivEquiv (H : Subgroup G) (e : G ≃* G') :
    H ≃* H.map (e : G →* G') :=
  H.equivMapOfInjective e.toMonoidHom e.injective

theorem mapMulEquivEquiv_coe_apply (H : Subgroup G) (e : G ≃* G')
    (h : H) :
    ((SchreierEquiv.Subgroup.mapMulEquivEquiv H e h : H.map (e : G →* G')) : G') = e (h : G) :=
  rfl

/-- Transport a subgroup by a multiplicative equivalence and then identify
its image with an equal target subgroup. -/
noncomputable def mapMulEquivEquivOfEq (H : Subgroup G) (e : G ≃* G')
    (H' : Subgroup G') (h : H.map (e : G →* G') = H') : H ≃* H' :=
  (SchreierEquiv.Subgroup.mapMulEquivEquiv H e).trans (MulEquiv.subgroupCongr h)

theorem mapMulEquivEquivOfEq_coe_apply (H : Subgroup G) (e : G ≃* G')
    (H' : Subgroup G') (h : H.map (e : G →* G') = H') (x : H) :
    ((SchreierEquiv.Subgroup.mapMulEquivEquivOfEq H e H' h x : H') : G') = e (x : G) := by
  subst H'
  rfl

end Subgroup

namespace Subgroup.RightTransversal

universe u v

variable {G : Type u} {G' : Type v} [Group G] [Group G'] {H : Subgroup G}

/-- The image of a representative from a right transversal under a
multiplicative equivalence. -/
def mapMulEquivRep (e : G ≃* G') (T : H.RightTransversal)
    (t : (T : Set G)) : G' :=
  e (t : G)

/-- The image set of a right transversal under a multiplicative
equivalence. -/
def mapMulEquivSet (e : G ≃* G') (T : H.RightTransversal) : Set G' :=
  Set.range (mapMulEquivRep e T)

/-- The representatives of a transversal are equivalent to the
representatives in its transported image. -/
noncomputable def mapMulEquivRangeEquiv (e : G ≃* G')
    (T : H.RightTransversal) :
    (T : Set G) ≃ ↥(mapMulEquivSet e T : Set G') :=
  Equiv.ofInjective (mapMulEquivRep e T)
    (e.injective.comp Subtype.val_injective)

theorem mapMulEquivRangeEquiv_coe_apply (e : G ≃* G')
    (T : H.RightTransversal)
    (t : (T : Set G)) :
    ((mapMulEquivRangeEquiv e T t :
      ↥(mapMulEquivSet e T : Set G')) : G') = e (t : G) :=
  rfl

/-- Transport a right transversal along a multiplicative equivalence. -/
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

/-- The canonical equivalence between the representatives of a transversal
and those of its transport. -/
noncomputable def mapMulEquivRepEquiv (e : G ≃* G')
    (T : H.RightTransversal) :
    (T : Set G) ≃ ((mapMulEquiv e T : Set G')) :=
  mapMulEquivRangeEquiv e T

theorem mapMulEquivRepEquiv_coe_apply (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) :
    ((mapMulEquivRepEquiv e T t : ((mapMulEquiv e T : Set G'))) : G') =
      e (t : G) :=
  rfl

/-- The Schreier decomposition of a transported transversal is the
transport of the original Schreier decomposition. -/
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

/-- Schreier representatives commute with transport of a transversal. -/
theorem mapMulEquiv_schreierRep (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) (g : G) :
    (mapMulEquiv e T).schreierRep (mapMulEquivRepEquiv e T t) (e g) =
      mapMulEquivRepEquiv e T (T.schreierRep t g) :=
  congrArg Prod.snd (mapMulEquiv_schreierDecomposition e T t g)

/-- Schreier factors commute with transport of a transversal. -/
theorem mapMulEquiv_schreierFactor (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) (g : G) :
    (mapMulEquiv e T).schreierFactor (mapMulEquivRepEquiv e T t) (e g) =
      SchreierEquiv.Subgroup.mapMulEquivEquiv H e (T.schreierFactor t g) :=
  congrArg Prod.fst (mapMulEquiv_schreierDecomposition e T t g)

end Subgroup.RightTransversal

namespace Subgroup.RightTransversal

universe u v

variable {G : Type u} {G' : Type v} [Group G] [Group G'] {H : Subgroup G}

/-- The full Schreier representative scan commutes with transport of a
right transversal along a multiplicative equivalence. -/
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

/-- The full Schreier factor tuple commutes with transport of a right
transversal along a multiplicative equivalence. -/
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

/-! The original one-universe API remains a compatibility surface. -/

namespace Subgroup

universe u

variable {G G' : Type u} [Group G] [Group G']

/-- The canonical equivalence from a subgroup to its image under a
multiplicative equivalence, with the image written using the underlying
monoid homomorphism. -/
noncomputable abbrev mapMulEquivEquiv (H : Subgroup G) (e : G ≃* G') :
    H ≃* H.map e.toMonoidHom :=
  SchreierEquiv.Subgroup.mapMulEquivEquiv H e

@[simp]
theorem mapMulEquivEquiv_coe_apply (H : Subgroup G) (e : G ≃* G')
    (h : H) :
    ((SchreierEquiv.Subgroup.mapMulEquivEquiv H e h : H.map (e : G →* G')) : G') = e (h : G) :=
  SchreierEquiv.Subgroup.mapMulEquivEquiv_coe_apply H e h

/-- Transport a subgroup by a multiplicative equivalence and then identify
its image with an equal target subgroup. -/
noncomputable abbrev mapMulEquivEquivOfEq (H : Subgroup G) (e : G ≃* G')
    (H' : Subgroup G') (h : H.map e.toMonoidHom = H') : H ≃* H' :=
  SchreierEquiv.Subgroup.mapMulEquivEquivOfEq H e H' h

@[simp]
theorem mapMulEquivEquivOfEq_coe_apply (H : Subgroup G) (e : G ≃* G')
    (H' : Subgroup G') (h : H.map e.toMonoidHom = H') (x : H) :
    ((H.mapMulEquivEquivOfEq e H' h x : H') : G') = e (x : G) :=
  SchreierEquiv.Subgroup.mapMulEquivEquivOfEq_coe_apply H e H' h x

end Subgroup

namespace Subgroup.RightTransversal

universe u

variable {G G' : Type u} [Group G] [Group G'] {H : Subgroup G}

/-- The image of a representative from a right transversal under a
multiplicative equivalence. -/
abbrev mapMulEquivRep (e : G ≃* G') (T : H.RightTransversal)
    (t : (T : Set G)) : G' :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquivRep e T t

/-- The image set of a right transversal under a multiplicative
equivalence. -/
abbrev mapMulEquivSet (e : G ≃* G') (T : H.RightTransversal) : Set G' :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquivSet e T

/-- The representatives of a transversal are equivalent to the
representatives in its transported image. -/
noncomputable abbrev mapMulEquivRangeEquiv (e : G ≃* G')
    (T : H.RightTransversal) :
    (T : Set G) ≃ ↥(mapMulEquivSet e T : Set G') :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquivRangeEquiv e T

@[simp]
theorem mapMulEquivRangeEquiv_coe_apply (e : G ≃* G')
    (T : H.RightTransversal)
    (t : (T : Set G)) :
    ((mapMulEquivRangeEquiv e T t :
      ↥(mapMulEquivSet e T : Set G')) : G') = e (t : G) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquivRangeEquiv_coe_apply e T t

/-- Transport a right transversal along a multiplicative equivalence. -/
noncomputable abbrev mapMulEquiv (e : G ≃* G') (T : H.RightTransversal) :
    (H.map e.toMonoidHom).RightTransversal :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv e T

/-- The canonical equivalence between the representatives of a transversal
and those of its transport. -/
noncomputable abbrev mapMulEquivRepEquiv (e : G ≃* G')
    (T : H.RightTransversal) :
    (T : Set G) ≃ ((mapMulEquiv e T : Set G')) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquivRepEquiv e T

@[simp]
theorem mapMulEquivRepEquiv_coe_apply (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) :
    ((mapMulEquivRepEquiv e T t : ((mapMulEquiv e T : Set G'))) : G') =
      e (t : G) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquivRepEquiv_coe_apply e T t

/-- The Schreier decomposition of a transported transversal is the
transport of the original Schreier decomposition. -/
theorem mapMulEquiv_schreierDecomposition (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) (g : G) :
    ((mapMulEquiv e T).schreierFactor (mapMulEquivRepEquiv e T t) (e g),
        (mapMulEquiv e T).schreierRep
          (mapMulEquivRepEquiv e T t) (e g)) =
      (H.mapMulEquivEquiv e (T.schreierFactor t g),
        mapMulEquivRepEquiv e T (T.schreierRep t g)) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv_schreierDecomposition e T t g

/-- Schreier representatives commute with transport of a transversal. -/
theorem mapMulEquiv_schreierRep (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) (g : G) :
    (mapMulEquiv e T).schreierRep (mapMulEquivRepEquiv e T t) (e g) =
      mapMulEquivRepEquiv e T (T.schreierRep t g) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv_schreierRep e T t g

/-- Schreier factors commute with transport of a transversal. -/
theorem mapMulEquiv_schreierFactor (e : G ≃* G')
    (T : H.RightTransversal) (t : (T : Set G)) (g : G) :
    (mapMulEquiv e T).schreierFactor (mapMulEquivRepEquiv e T t) (e g) =
      H.mapMulEquivEquiv e (T.schreierFactor t g) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv_schreierFactor e T t g

end Subgroup.RightTransversal

namespace Subgroup.RightTransversal

universe u

variable {G G' : Type u} [Group G] [Group G'] {H : Subgroup G}

/-- The full Schreier representative scan commutes with transport of a
right transversal along a multiplicative equivalence. -/
theorem mapMulEquiv_schreierRepScan {n : ℕ}
    (e : G ≃* G') (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) (i : Fin (n + 1)) :
    (T.mapMulEquiv e).schreierRepScan
        (T.mapMulEquivRepEquiv e t) (fun j ↦ e (g j)) i =
      T.mapMulEquivRepEquiv e (T.schreierRepScan t g i) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv_schreierRepScan e T t g i

/-- The full Schreier factor tuple commutes with transport of a right
transversal along a multiplicative equivalence. -/
theorem mapMulEquiv_schreierFactorTuple {n : ℕ}
    (e : G ≃* G') (T : H.RightTransversal)
    (t : (T : Set G)) (g : Fin n → G) :
    (T.mapMulEquiv e).schreierFactorTuple
        (T.mapMulEquivRepEquiv e t) (fun j ↦ e (g j)) =
      fun i ↦ H.mapMulEquivEquiv e (T.schreierFactorTuple t g i) :=
  SchreierEquiv.Subgroup.RightTransversal.mapMulEquiv_schreierFactorTuple e T t g

end Subgroup.RightTransversal
