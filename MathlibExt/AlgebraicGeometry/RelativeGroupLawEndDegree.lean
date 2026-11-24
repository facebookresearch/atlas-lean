/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean`,
`Definitions/Def_GoodReductionJacobian_RelativeGroupLawKernel.lean` and
`Definitions/Def_AlgebraicGeometry_RelativeGroupLawEndDegree.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import MathlibExt.AlgebraicGeometry.RelativeGroupLaw
public import MathlibExt.AlgebraicGeometry.SchemeHomOver

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

/-- A relative group law is commutative when its multiplication on points
over every test scheme is commutative. -/
def IsCommutative (G : RelativeGroupLaw R f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : Over.mk t ⟶ Over.mk f), G.mul t x y = G.mul t y x

theorem IsCommutative.mul_comm {G : RelativeGroupLaw R f} (hc : G.IsCommutative)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : Over.mk t ⟶ Over.mk f) : G.mul t x y = G.mul t y x :=
  hc t x y

/-- The commutative group structure on points of a commutative relative
group law over a fixed test scheme. -/
@[reducible]
def pointCommGroup (G : RelativeGroupLaw R f) (hc : G.IsCommutative)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    CommGroup (Over.mk t ⟶ Over.mk f) :=
  { G.pointGroup t with mul_comm := fun x y => hc t x y }

/-- The `n`-fold sum of a point under a relative group law. -/
def nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : Over.mk t ⟶ Over.mk f) :
    Over.mk t ⟶ Over.mk f :=
  Nat.rec (G.one t) (fun _ ih => G.mul t ih x) n

@[simp]
theorem nsmul_zero (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : Over.mk t ⟶ Over.mk f) :
    G.nsmul t 0 x = G.one t :=
  rfl

@[simp]
theorem nsmul_succ (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : Over.mk t ⟶ Over.mk f) :
    G.nsmul t (n + 1) x = G.mul t (G.nsmul t n x) x :=
  rfl

theorem nsmul_one (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : Over.mk t ⟶ Over.mk f) :
    G.nsmul t 1 x = x :=
  G.one_mul t x

theorem nsmul_one_point (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    G.nsmul t n (G.one t) = G.one t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsmul_succ, ih, G.mul_one]

/-- The identity endomorphism of `A` over the base, as a point of the
relative group law over the base itself. -/
noncomputable def idPoint : SchemeHomOver f f :=
  Over.homMk (𝟙 A) (Category.id_comp f)

/-- The identity endomorphism over the base. -/
noncomputable def idEnd : SchemeHomOver f f :=
  idPoint

theorem idEnd_left : (idEnd (f := f)).left = 𝟙 A :=
  rfl

/-- Multiplication by `n` as a scheme endomorphism over the base. -/
noncomputable def schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) : A ⟶ A :=
  (G.nsmul f n idPoint).left

theorem schemeNsmul_comp (G : RelativeGroupLaw R f) (n : ℕ) :
    G.schemeNsmul n ≫ f = f :=
  Over.w (G.nsmul f n idPoint)

/-- The scheme-theoretic kernel of multiplication by `n`: the pullback of
multiplication by `n` along the identity section. -/
noncomputable def schemeKer (G : RelativeGroupLaw R f) (n : ℕ) : Scheme.{u} :=
  pullback (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).left

/-- The structure morphism of the kernel of multiplication by `n`. -/
noncomputable def schemeKerStr (G : RelativeGroupLaw R f) (n : ℕ) :
    G.schemeKer n ⟶ Spec (CommRingCat.of R) :=
  pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).left

section Field

variable {K : Type u} [Field K] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of K)}

/-- The kernel scheme of a scheme endomorphism over the base: the pullback
of the endomorphism along the identity section. -/
noncomputable def endKer (G : RelativeGroupLaw K g) (β : SchemeHomOver g g) : Scheme.{u} :=
  pullback β.left (G.one (𝟙 (Spec (CommRingCat.of K)))).left

/-- The structure morphism of the kernel of a scheme endomorphism. -/
noncomputable def endKerStr (G : RelativeGroupLaw K g) (β : SchemeHomOver g g) :
    G.endKer β ⟶ Spec (CommRingCat.of K) :=
  pullback.snd β.left (G.one (𝟙 (Spec (CommRingCat.of K)))).left

/-- The inclusion of the kernel of a scheme endomorphism into `B`. -/
noncomputable def endKerι (G : RelativeGroupLaw K g) (β : SchemeHomOver g g) :
    G.endKer β ⟶ B :=
  pullback.fst β.left (G.one (𝟙 (Spec (CommRingCat.of K)))).left

theorem endKerι_comp (G : RelativeGroupLaw K g) (β : SchemeHomOver g g) :
    G.endKerι β ≫ β.left =
      G.endKerStr β ≫ (G.one (𝟙 (Spec (CommRingCat.of K)))).left :=
  pullback.condition

/-- The degree of a scheme endomorphism of a relative group law over a
field: the rank at the closed point of its kernel when the kernel is
finite over the base, and `0` otherwise. -/
noncomputable def endDegree (G : RelativeGroupLaw K g) (β : SchemeHomOver g g) :
    ℕ := by
  classical
  exact if IsFinite (G.endKerStr β) then
    (G.endKerStr β).finrank (IsLocalRing.closedPoint K) else 0

theorem endDegree_of_isFinite (G : RelativeGroupLaw K g) (β : SchemeHomOver g g)
    [h : IsFinite (G.endKerStr β)] :
    G.endDegree β = (G.endKerStr β).finrank (IsLocalRing.closedPoint K) := by
  rw [endDegree, if_pos h]

theorem endDegree_of_not_isFinite (G : RelativeGroupLaw K g) (β : SchemeHomOver g g)
    (h : ¬ IsFinite (G.endKerStr β)) : G.endDegree β = 0 := by
  rw [endDegree, if_neg h]

theorem endKer_nsmul_idPoint (G : RelativeGroupLaw K g) (n : ℕ) :
    G.endKer (G.nsmul g n idPoint) = G.schemeKer n :=
  rfl

instance isIso_endKerStr_idEnd (G : RelativeGroupLaw K g) :
    IsIso (G.endKerStr (idEnd (f := g))) := by
  change IsIso (pullback.snd (𝟙 B) (G.one (𝟙 (Spec (CommRingCat.of K)))).left)
  infer_instance

theorem endDegree_idEnd (G : RelativeGroupLaw K g) :
    G.endDegree (idEnd (f := g)) = 1 := by
  haveI : IsFinite (G.endKerStr (idEnd (f := g))) := inferInstance
  rw [endDegree_of_isFinite]
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso _) _

end Field

end RelativeGroupLaw

end AlgebraicGeometry
