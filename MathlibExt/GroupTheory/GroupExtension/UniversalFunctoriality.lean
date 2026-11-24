/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.GroupTheory.GroupExtension.Hom
public import MathlibExt.GroupTheory.GroupExtension.Pullback

/-!
# Canonical lifts from universal central extensions

A base homomorphism lifts from a universal central extension through a
central target extension by the original central pullback. The universality
scope records the kernel universe of the target and the total universe of
that actual pullback. The resulting total, kernel and quotient maps retain
the original extension squares.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uN uE uG vN vE vG wN wE wG

namespace GroupExtension

variable {N : Type uN} {E : Type uE} {G : Type uG}
variable {K : Type vN} {D : Type vE} {H : Type vG}
variable [Group N] [Group E] [Group G] [Group K] [Group D] [Group H]
variable {S : GroupExtension N E G} {T : GroupExtension K D H}

namespace IsUniversalFor

/-- The unique original map to the central pullback supplied by source universality. -/
def liftToPullback
    (hS : IsUniversalFor.{uN, uE, uG, vN, max uG vE} S)
    (T : GroupExtension K D H) (hT : T.IsCentral) (f : G →* H) :
    E →* PullbackTotal T f :=
  (hS.2 (pullbackExtension T f) (pullback_isCentral T f hT)).choose

/-- The canonical pullback lift retains the original source projection. -/
theorem liftToPullback_square
    (hS : IsUniversalFor.{uN, uE, uG, vN, max uG vE} S)
    (T : GroupExtension K D H) (hT : T.IsCentral) (f : G →* H) :
    (pullbackSnd T f).comp (liftToPullback hS T hT f) = S.rightHom :=
  (hS.2 (pullbackExtension T f) (pullback_isCentral T f hT)).choose_spec.1

/-- The canonical original total lift through a central extension over a base homomorphism. -/
def lift (hS : IsUniversalFor.{uN, uE, uG, vN, max uG vE} S)
    (T : GroupExtension K D H) (hT : T.IsCentral) (f : G →* H) : E →* D :=
  (pullbackFst T f).comp (liftToPullback hS T hT f)

/-- The canonical lift satisfies the whole original projection square. -/
@[simp]
theorem rightHom_comp_lift
    (hS : IsUniversalFor.{uN, uE, uG, vN, max uG vE} S)
    (T : GroupExtension K D H) (hT : T.IsCentral) (f : G →* H) :
    T.rightHom.comp (lift hS T hT f) = f.comp S.rightHom := by
  rw [lift, ← MonoidHom.comp_assoc, pullback_square, MonoidHom.comp_assoc,
    liftToPullback_square]

/-- Any original total map over the same base homomorphism equals the canonical lift. -/
theorem lift_unique
    (hS : IsUniversalFor.{uN, uE, uG, vN, max uG vE} S)
    (T : GroupExtension K D H) (hT : T.IsCentral) (f : G →* H)
    (φ : E →* D) (hφ : T.rightHom.comp φ = f.comp S.rightHom) :
    φ = lift hS T hT f := by
  let q : E →* PullbackTotal T f := pullbackLift T φ S.rightHom hφ
  have hq : (pullbackSnd T f).comp q = S.rightHom :=
    pullbackSnd_comp_pullbackLift T
  have hunique : q = liftToPullback hS T hT f :=
    (hS.2 (pullbackExtension T f) (pullback_isCentral T f hT)).choose_spec.2 q hq
  calc
    φ = (pullbackFst T f).comp q := (pullbackFst_comp_pullbackLift T).symm
    _ = (pullbackFst T f).comp (liftToPullback hS T hT f) := by rw [hunique]
    _ = lift hS T hT f := rfl

/-- The canonical lift bundled with the induced original kernel and quotient maps. -/
def liftHom (hS : IsUniversalFor.{uN, uE, uG, vN, max uG vE} S)
    (T : GroupExtension K D H) (hT : T.IsCentral) (f : G →* H) : S.Hom T :=
  Hom.ofTotal (lift hS T hT f) f (rightHom_comp_lift hS T hT f)

@[simp]
theorem liftHom_totalHom
    (hS : IsUniversalFor.{uN, uE, uG, vN, max uG vE} S)
    (T : GroupExtension K D H) (hT : T.IsCentral) (f : G →* H) :
    (liftHom hS T hT f).totalHom = lift hS T hT f := rfl

@[simp]
theorem liftHom_quotientHom
    (hS : IsUniversalFor.{uN, uE, uG, vN, max uG vE} S)
    (T : GroupExtension K D H) (hT : T.IsCentral) (f : G →* H) :
    (liftHom hS T hT f).quotientHom = f := rfl

/-- The canonical total lift of the original identity base map is the identity. -/
@[simp]
theorem lift_id (hS : IsUniversalFor.{uN, uE, uG, uN, max uG uE} S) :
    lift hS S hS.1 (MonoidHom.id G) = MonoidHom.id E := by
  symm
  apply lift_unique hS S hS.1 (MonoidHom.id G)
  simp

/-- The canonical identity lift preserves all original extension maps. -/
@[simp]
theorem liftHom_id (hS : IsUniversalFor.{uN, uE, uG, uN, max uG uE} S) :
    liftHom hS S hS.1 (MonoidHom.id G) = Hom.id S := by
  apply Hom.ext
  exact lift_id hS

section Composition

variable {L : Type wN} {F : Type wE} {J : Type wG}
variable [Group L] [Group F] [Group J]
variable {U : GroupExtension L F J}

/-- Canonical original total lifts preserve composition of base homomorphisms. -/
theorem lift_comp
    (hST : IsUniversalFor.{uN, uE, uG, vN, max uG vE} S)
    (hTU : IsUniversalFor.{vN, vE, vG, wN, max vG wE} T)
    (hSU : IsUniversalFor.{uN, uE, uG, wN, max uG wE} S)
    (U : GroupExtension L F J) (hU : U.IsCentral) (f : G →* H) (g : H →* J) :
    lift hSU U hU (g.comp f) = (lift hTU U hU g).comp (lift hST T hTU.1 f) := by
  symm
  apply lift_unique hSU U hU (g.comp f)
  rw [← MonoidHom.comp_assoc, rightHom_comp_lift, MonoidHom.comp_assoc,
    rightHom_comp_lift, ← MonoidHom.comp_assoc]

/-- Canonical lift morphisms preserve the whole original composition diagram. -/
theorem liftHom_comp
    (hST : IsUniversalFor.{uN, uE, uG, vN, max uG vE} S)
    (hTU : IsUniversalFor.{vN, vE, vG, wN, max vG wE} T)
    (hSU : IsUniversalFor.{uN, uE, uG, wN, max uG wE} S)
    (U : GroupExtension L F J) (hU : U.IsCentral) (f : G →* H) (g : H →* J) :
    liftHom hSU U hU (g.comp f) =
      (liftHom hTU U hU g).comp (liftHom hST T hTU.1 f) := by
  apply Hom.ext
  exact lift_comp hST hTU hSU U hU f g

/-- The original kernel maps of canonical lifts preserve composition. -/
theorem liftHom_kernelHom_comp
    (hST : IsUniversalFor.{uN, uE, uG, vN, max uG vE} S)
    (hTU : IsUniversalFor.{vN, vE, vG, wN, max vG wE} T)
    (hSU : IsUniversalFor.{uN, uE, uG, wN, max uG wE} S)
    (U : GroupExtension L F J) (hU : U.IsCentral) (f : G →* H) (g : H →* J) :
    (liftHom hSU U hU (g.comp f)).kernelHom =
      (liftHom hTU U hU g).kernelHom.comp (liftHom hST T hTU.1 f).kernelHom := by
  rw [liftHom_comp hST hTU hSU U hU f g, Hom.comp_kernelHom]

end Composition

/-- The original kernel map of a canonical identity lift is the identity. -/
theorem liftHom_kernelHom_id (hS : IsUniversalFor.{uN, uE, uG, uN, max uG uE} S) :
    (liftHom hS S hS.1 (MonoidHom.id G)).kernelHom = MonoidHom.id N := by
  rw [liftHom_id hS, Hom.id_kernelHom]

end IsUniversalFor

end GroupExtension
