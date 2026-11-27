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

/-!
# Degrees of endomorphisms of relative group laws

An endomorphism of a relative group law is a scheme endomorphism over the base
that preserves the group law on points over every test scheme. Its kernel is
the pullback of the endomorphism along the identity section, and over a field
its degree is the rank of the kernel at the closed point when the kernel is
finite over the base, and `0` otherwise. On a commutative law, multiplication
by `n` is such an endomorphism.

The source states the kernel and the degree for an arbitrary scheme
endomorphism over the base; here they take an endomorphism of the law, so
that the pullback along the identity section is a kernel.
-/

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

/-- The `n`-fold sum of a point is its `n`-th power in the group of points. -/
theorem nsmul_eq_pow (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : Over.mk t ⟶ Over.mk f) :
    letI := G.pointGroup t
    G.nsmul t n x = x ^ n := by
  let := G.pointGroup t
  induction n with
  | zero =>
    rw [nsmul_zero, pow_zero]
    rfl
  | succ n ih =>
    rw [nsmul_succ, ih, pow_succ]
    rfl

/-- On a commutative relative group law, the `n`-fold sum of a product of
points is the product of their `n`-fold sums. -/
theorem IsCommutative.nsmul_mul {G : RelativeGroupLaw R f} (hc : G.IsCommutative)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x y : Over.mk t ⟶ Over.mk f) :
    G.nsmul t n (G.mul t x y) = G.mul t (G.nsmul t n x) (G.nsmul t n y) := by
  let := G.pointCommGroup hc t
  simp only [G.nsmul_eq_pow]
  exact mul_pow x y n

/-- The `n`-fold sum commutes with base change of points along a morphism of
test schemes over the base. -/
theorem homMk_comp_nsmul (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : Over.mk t ⟶ Over.mk f) :
    Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ G.nsmul t n x =
      G.nsmul t' n (Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ x) := by
  induction n with
  | zero => exact G.one_natural t t' ψ hψ
  | succ n ih => rw [nsmul_succ, nsmul_succ, G.mul_natural, ih]

/-- The identity endomorphism of `A` over the base, as a point of the
relative group law over the base itself. -/
noncomputable def idPoint : SchemeHomOver f f :=
  Over.homMk (𝟙 A) (Category.id_comp f)

@[simp]
theorem comp_idPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : Over.mk t ⟶ Over.mk f) : x ≫ idPoint = x :=
  Over.OverMorphism.ext (by simp [idPoint])

/-- Composing a point with the `n`-fold sum of the universal point gives the
`n`-fold sum of the point. -/
theorem comp_nsmul_idPoint (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : Over.mk t ⟶ Over.mk f) :
    x ≫ G.nsmul f n idPoint = G.nsmul t n x := by
  have h := G.homMk_comp_nsmul f t x.left (Over.w x) n idPoint
  have hx : Over.homMk (U := Over.mk t) (V := Over.mk f) x.left (Over.w x) = x :=
    Over.OverMorphism.ext rfl
  rwa [comp_idPoint, hx] at h

/-- An endomorphism of a relative group law: a scheme endomorphism over the
base whose action on points over every test scheme preserves the group law. -/
@[ext]
structure End (G : RelativeGroupLaw R f) where
  /-- The underlying scheme endomorphism over the base. -/
  hom : SchemeHomOver f f
  /-- Composition with the endomorphism preserves the product of points. -/
  map_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : Over.mk t ⟶ Over.mk f), G.mul t x y ≫ hom = G.mul t (x ≫ hom) (y ≫ hom)

/-- An endomorphism of a relative group law fixes the identity point. -/
theorem End.map_one {G : RelativeGroupLaw R f} (β : G.End) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : G.one t ≫ β.hom = G.one t := by
  let := G.pointGroup t
  refine mul_left_cancel (a := G.one t ≫ β.hom) (c := 1) ?_
  change G.mul t (G.one t ≫ β.hom) (G.one t ≫ β.hom) = G.mul t (G.one t ≫ β.hom) (G.one t)
  rw [← β.map_mul, G.one_mul, G.mul_one]

/-- The identity endomorphism of a relative group law. -/
noncomputable def idEnd (G : RelativeGroupLaw R f) : G.End where
  hom := idPoint
  map_mul t x y := by simp only [comp_idPoint]

theorem idEnd_left (G : RelativeGroupLaw R f) : G.idEnd.hom.left = 𝟙 A :=
  rfl

/-- Multiplication by `n` on a commutative relative group law, as an
endomorphism of the law. -/
noncomputable def nsmulEnd (G : RelativeGroupLaw R f) (hc : G.IsCommutative) (n : ℕ) :
    G.End where
  hom := G.nsmul f n idPoint
  map_mul t x y := by
    simp only [comp_nsmul_idPoint]
    exact hc.nsmul_mul t n x y

@[simp]
theorem nsmulEnd_hom (G : RelativeGroupLaw R f) (hc : G.IsCommutative) (n : ℕ) :
    (G.nsmulEnd hc n).hom = G.nsmul f n idPoint :=
  rfl

/-- Multiplication by `n` as a scheme endomorphism over the base. On a
commutative law it underlies the endomorphism `nsmulEnd`. -/
noncomputable def schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) : A ⟶ A :=
  (G.nsmul f n idPoint).left

theorem schemeNsmul_comp (G : RelativeGroupLaw R f) (n : ℕ) :
    G.schemeNsmul n ≫ f = f :=
  Over.w (G.nsmul f n idPoint)

theorem nsmulEnd_hom_left (G : RelativeGroupLaw R f) (hc : G.IsCommutative) (n : ℕ) :
    (G.nsmulEnd hc n).hom.left = G.schemeNsmul n :=
  rfl

/-- The scheme-theoretic kernel of multiplication by `n` on a commutative
relative group law: the pullback of multiplication by `n` along the identity
section. -/
noncomputable def schemeKer (G : RelativeGroupLaw R f) (hc : G.IsCommutative) (n : ℕ) :
    Scheme.{u} :=
  pullback (G.nsmulEnd hc n).hom.left (G.one (𝟙 (Spec (CommRingCat.of R)))).left

/-- The structure morphism of the kernel of multiplication by `n`. -/
noncomputable def schemeKerStr (G : RelativeGroupLaw R f) (hc : G.IsCommutative) (n : ℕ) :
    G.schemeKer hc n ⟶ Spec (CommRingCat.of R) :=
  pullback.snd (G.nsmulEnd hc n).hom.left (G.one (𝟙 (Spec (CommRingCat.of R)))).left

/-- The kernel of an endomorphism of a relative group law: the pullback of
the endomorphism along the identity section. -/
noncomputable def endKer (G : RelativeGroupLaw R f) (β : G.End) : Scheme.{u} :=
  pullback β.hom.left (G.one (𝟙 (Spec (CommRingCat.of R)))).left

/-- The structure morphism of the kernel of an endomorphism. -/
noncomputable def endKerStr (G : RelativeGroupLaw R f) (β : G.End) :
    G.endKer β ⟶ Spec (CommRingCat.of R) :=
  pullback.snd β.hom.left (G.one (𝟙 (Spec (CommRingCat.of R)))).left

/-- The inclusion of the kernel of an endomorphism into `A`. -/
noncomputable def endKerι (G : RelativeGroupLaw R f) (β : G.End) :
    G.endKer β ⟶ A :=
  pullback.fst β.hom.left (G.one (𝟙 (Spec (CommRingCat.of R)))).left

theorem endKerι_comp (G : RelativeGroupLaw R f) (β : G.End) :
    G.endKerι β ≫ β.hom.left =
      G.endKerStr β ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).left :=
  pullback.condition

/-- The kernel of multiplication by `n`, as an endomorphism, is `schemeKer`. -/
theorem endKer_nsmulEnd (G : RelativeGroupLaw R f) (hc : G.IsCommutative) (n : ℕ) :
    G.endKer (G.nsmulEnd hc n) = G.schemeKer hc n :=
  rfl

instance isIso_endKerStr_idEnd (G : RelativeGroupLaw R f) :
    IsIso (G.endKerStr G.idEnd) := by
  change IsIso (pullback.snd (𝟙 A) (G.one (𝟙 (Spec (CommRingCat.of R)))).left)
  infer_instance

section Field

variable {K : Type u} [Field K] {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of K)}

/-- The degree of an endomorphism of a relative group law over a field: the
rank at the closed point of its kernel when the kernel is finite over the
base, and `0` otherwise. -/
noncomputable def endDegree (G : RelativeGroupLaw K g) (β : G.End) : ℕ := by
  classical
  exact if IsFinite (G.endKerStr β) then
    (G.endKerStr β).finrank (IsLocalRing.closedPoint K) else 0

theorem endDegree_of_isFinite (G : RelativeGroupLaw K g) (β : G.End)
    [h : IsFinite (G.endKerStr β)] :
    G.endDegree β = (G.endKerStr β).finrank (IsLocalRing.closedPoint K) := by
  rw [endDegree, ite_eq_left h]

theorem endDegree_of_not_isFinite (G : RelativeGroupLaw K g) (β : G.End)
    (h : ¬ IsFinite (G.endKerStr β)) : G.endDegree β = 0 := by
  rw [endDegree, ite_eq_right h]

/-- When the kernel of multiplication by `n` is finite over the base, the
degree of multiplication by `n` is the rank of that kernel at the closed
point. -/
theorem endDegree_nsmulEnd (G : RelativeGroupLaw K g) (hc : G.IsCommutative) (n : ℕ)
    [IsFinite (G.schemeKerStr hc n)] :
    G.endDegree (G.nsmulEnd hc n) =
      (G.schemeKerStr hc n).finrank (IsLocalRing.closedPoint K) :=
  have : IsFinite (G.endKerStr (G.nsmulEnd hc n)) := ‹IsFinite (G.schemeKerStr hc n)›
  G.endDegree_of_isFinite (G.nsmulEnd hc n)

theorem endDegree_idEnd (G : RelativeGroupLaw K g) :
    G.endDegree G.idEnd = 1 := by
  rw [endDegree_of_isFinite]
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso _) _

end Field

end RelativeGroupLaw

end AlgebraicGeometry
