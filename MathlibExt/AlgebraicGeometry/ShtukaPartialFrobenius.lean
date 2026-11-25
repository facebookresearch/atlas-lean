/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/NumberTheory/Drinfeld/Shtuka/Basic.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b):
Copyright (c) 2026 the Stacks project formalization contributors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: specialize to the prime field, use the Zariski bundle trivializations of this
repository, and add the sheaf-module pushout describing the pole partial-Frobenius modification.
Its geometric bundle and cokernel conditions are separated from the completed categorical
construction.
-/
module

public import MathlibExt.AlgebraicGeometry.FrobeniusGeometry
public import MathlibExt.AlgebraicGeometry.CurveVectorBundles
public import MathlibExt.AlgebraicGeometry.FlatCokernelBaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
# Actual right shtukas and their pole modification

The scheme is `X ×_{F_p} S`. A right shtuka has actual rank-`r` bundles
`E → E' ← τ*E`, with graph-line cokernels. Here `τ = id_X × Frob_S`.
The fixed candidate for the pole partial-Frobenius has bundles
`E' → E' ⨿_{τ*E} τ*E' ← τ*E'`. The arrows are the actual pushout arrows;
the pole becomes `Frob_X ∘ pole` and the zero is unchanged.

This file completes that candidate and its categorical maps. The graph
cokernel and injectivity of the pulled-back pole modification are covered,
for a separated curve, by Axiom's `Shtuka/BaseChange.lean` (same revision),
via closed graphs, graph-line flatness and actual affine base change. Their
precise input is recorded below and transported through the canonical
pushout cokernel map. The remaining
request is the rank/local-freeness of the fixed pushout on disjoint legs.

References: Drinfeld, *Cohomology of compactified manifolds of modules of
F-sheaves of rank 2*, J. Soviet Math. 46 (1989); Bieker,
*Compactification of level maps of moduli spaces of Drinfeld shtukas*,
Definition 2.2 and Remark 2.3, https://arxiv.org/abs/2205.09371.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ShtukaPartialFrobenius

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open FrobeniusGeometry CoherentCurveLinearSeries CurveVectorBundles

variable (p : ℕ) [Fact p.Prime]

abbrev PrimeFieldScheme := Over (Spec (CommRingCat.of.{0} (ZMod p)))

variable (X S : PrimeFieldScheme p)

/-- The actual curve-family product. -/
abbrev product : Scheme := pullback X.hom S.hom

/-- Frobenius acts on the base of the bundle family. -/
def twist : product p X S ⟶ product p X S :=
  pullback.map X.hom S.hom X.hom S.hom (𝟙 _)
    (primeFieldFrobenius p S).left (𝟙 _)
    (by simp) (by rw [Category.comp_id, Over.w])

@[reassoc (attr := simp)]
theorem twist_fst :
    twist p X S ≫ pullback.fst X.hom S.hom =
      pullback.fst X.hom S.hom :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
theorem twist_snd :
    twist p X S ≫ pullback.snd X.hom S.hom =
      pullback.snd X.hom S.hom ≫ (primeFieldFrobenius p S).left :=
  pullback.lift_snd _ _ _

variable {p X S}

/-- The leg is its actual graph in the family product. -/
def graph (x : S ⟶ X) : S.left ⟶ product p X S :=
  pullback.lift x.left (𝟙 _) (by rw [Category.id_comp, Over.w])

omit [Fact p.Prime] in
@[reassoc (attr := simp)]
theorem graph_fst (x : S ⟶ X) :
    graph x ≫ pullback.fst X.hom S.hom = x.left :=
  pullback.lift_fst _ _ _

omit [Fact p.Prime] in
@[reassoc (attr := simp)]
theorem graph_snd (x : S ⟶ X) :
    graph x ≫ pullback.snd X.hom S.hom = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- Cokernel support includes the scheme structure, via graph pushforward. -/
def IsGraphLineBundle (Q : (product p X S).Modules) (x : S ⟶ X) : Prop :=
  ∃ L : S.left.Modules, IsLineBundle L ∧
    Nonempty (Q ≅ (Scheme.Modules.pushforward (graph x)).obj L)

omit [Fact p.Prime] in
/-- The actual graph-line condition is invariant under module isomorphism. -/
theorem IsGraphLineBundle.of_iso {Q Q' : (product p X S).Modules}
    (e : Q ≅ Q') {x : S ⟶ X} (h : IsGraphLineBundle Q x) :
    IsGraphLineBundle Q' x := by
  obtain ⟨L, hL, ⟨e'⟩⟩ := h
  exact ⟨L, hL, ⟨e.symm ≪≫ e'⟩⟩

/-- Actual minuscule right-shtuka data. -/
structure Shtuka (p : ℕ) [Fact p.Prime]
    (X S : PrimeFieldScheme p) (r : ℕ) where
  E : (product p X S).Modules
  E' : (product p X S).Modules
  bundle_E : IsVectorBundle E r
  bundle_E' : IsVectorBundle E' r
  j : E ⟶ E'
  t : (Scheme.Modules.pullback (twist p X S)).obj E ⟶ E'
  mono_j : Mono j
  mono_t : Mono t
  pole : S ⟶ X
  zero : S ⟶ X
  cokernel_j : IsGraphLineBundle (cokernel j) pole
  cokernel_t : IsGraphLineBundle (cokernel t) zero

attribute [instance] Shtuka.mono_j Shtuka.mono_t

namespace Shtuka

variable {r : ℕ}

@[ext]
structure Hom (A B : Shtuka p X S r) where
  hom : A.E ⟶ B.E
  hom' : A.E' ⟶ B.E'
  pole_eq : A.pole = B.pole
  zero_eq : A.zero = B.zero
  j_comp : A.j ≫ hom' = hom ≫ B.j
  t_comp : A.t ≫ hom' =
    (Scheme.Modules.pullback (twist p X S)).map hom ≫ B.t

attribute [reassoc] Hom.j_comp Hom.t_comp

instance : Category (Shtuka p X S r) where
  Hom := Hom
  id A :=
    { hom := 𝟙 _
      hom' := 𝟙 _
      pole_eq := rfl
      zero_eq := rfl
      j_comp := by simp
      t_comp := by simp }
  comp a b :=
    { hom := a.hom ≫ b.hom
      hom' := a.hom' ≫ b.hom'
      pole_eq := a.pole_eq.trans b.pole_eq
      zero_eq := a.zero_eq.trans b.zero_eq
      j_comp := by rw [a.j_comp_assoc, b.j_comp, Category.assoc]
      t_comp := by
        rw [a.t_comp_assoc, b.t_comp, Functor.map_comp, Category.assoc] }

@[simp]
theorem id_hom (A : Shtuka p X S r) : (𝟙 A : A ⟶ A).hom = 𝟙 _ := rfl

@[simp]
theorem id_hom' (A : Shtuka p X S r) :
    (𝟙 A : A ⟶ A).hom' = 𝟙 _ := rfl

@[simp]
theorem comp_hom {A B C : Shtuka p X S r} (a : A ⟶ B) (b : B ⟶ C) :
    (a ≫ b).hom = a.hom ≫ b.hom := rfl

@[simp]
theorem comp_hom' {A B C : Shtuka p X S r} (a : A ⟶ B) (b : B ⟶ C) :
    (a ≫ b).hom' = a.hom' ≫ b.hom' := rfl

/-- The candidate second bundle is this fixed sheaf-module pushout. -/
abbrev rotationModule (A : Shtuka p X S r) :
    (product p X S).Modules :=
  pushout A.t ((Scheme.Modules.pullback (twist p X S)).map A.j)

abbrev rotationJ (A : Shtuka p X S r) : A.E' ⟶ A.rotationModule :=
  pushout.inl _ _

abbrev rotationT (A : Shtuka p X S r) :
    (Scheme.Modules.pullback (twist p X S)).obj A.E' ⟶ A.rotationModule :=
  pushout.inr _ _

/-- The pole moves by the actual curve Frobenius. -/
def rotationPole (A : Shtuka p X S r) : S ⟶ X :=
  A.pole ≫ primeFieldFrobenius p X

/-- The fixed candidate square is cocartesian, not a chosen new bundle map. -/
@[reassoc]
theorem rotation_square (A : Shtuka p X S r) :
    A.t ≫ A.rotationJ =
      (Scheme.Modules.pullback (twist p X S)).map A.j ≫ A.rotationT :=
  pushout.condition

/-- Pushout preserves the original modification's injectivity. -/
instance rotationT_mono (A : Shtuka p X S r) : Mono A.rotationT :=
  inferInstance

/-- Injectivity of the pulled-back pole modification suffices for the
other actual pushout arrow. -/
instance rotationJ_mono (A : Shtuka p X S r)
    [Mono ((Scheme.Modules.pullback (twist p X S)).map A.j)] :
    Mono A.rotationJ := inferInstance

/-- This comparison is the actual cokernel map of the pushout square. -/
def rotationCokernelTComparison (A : Shtuka p X S r) :
    cokernel A.t ⟶ cokernel A.rotationT :=
  cokernel.map A.t A.rotationT
    ((Scheme.Modules.pullback (twist p X S)).map A.j)
    A.rotationJ A.rotation_square

/-- Mathlib's pushout universal property proves the comparison invertible. -/
instance rotationCokernelTComparison_isIso (A : Shtuka p X S r) :
    IsIso A.rotationCokernelTComparison :=
  isIso_cokernel_map_of_isPushout
    (IsPushout.of_hasPushout A.t
      ((Scheme.Modules.pullback (twist p X S)).map A.j))

/-- The zero-leg graph-line cokernel is already a completed consequence
of that canonical comparison. -/
theorem rotationT_cokernel (A : Shtuka p X S r) :
    IsGraphLineBundle (cokernel A.rotationT) A.zero :=
  IsGraphLineBundle.of_iso (asIso A.rotationCokernelTComparison) A.cokernel_t

/-- The canonical comparison for the pole arrow uses the flipped pushout square. -/
def rotationCokernelJComparison (A : Shtuka p X S r) :
    cokernel ((Scheme.Modules.pullback (twist p X S)).map A.j) ⟶
      cokernel A.rotationJ :=
  cokernel.map ((Scheme.Modules.pullback (twist p X S)).map A.j)
    A.rotationJ A.t A.rotationT A.rotation_square.symm

instance rotationCokernelJComparison_isIso (A : Shtuka p X S r) :
    IsIso A.rotationCokernelJComparison :=
  isIso_cokernel_map_of_isPushout
    (IsPushout.of_hasPushout A.t
      ((Scheme.Modules.pullback (twist p X S)).map A.j)).flip

/-- Exact known source prerequisites on the actual Frobenius pullback.
`Shtuka/BaseChange.lean` proves these for a separated curve (closed graphs)
from graph-line flatness under any base change; here they are requested as
`WantedExt.AlgebraicGeometry.ShtukaPartialFrobenius.pullbackConditions`. The algebraic Tor step is
ported complete in `FlatCokernelBaseChange`. -/
structure PullbackConditions (A : Shtuka p X S r) : Prop where
  mono : Mono ((Scheme.Modules.pullback (twist p X S)).map A.j)
  cokernel : IsGraphLineBundle
    (cokernel ((Scheme.Modules.pullback (twist p X S)).map A.j)) A.rotationPole

theorem rotationJ_cokernel (A : Shtuka p X S r) (P : A.PullbackConditions) :
    IsGraphLineBundle (cokernel A.rotationJ) A.rotationPole :=
  IsGraphLineBundle.of_iso (asIso A.rotationCokernelJComparison) P.cokernel

/-- Geometric conditions remaining for this exact pushout construction. -/
structure RotationConditions (A : Shtuka p X S r) : Prop where
  bundle : IsVectorBundle A.rotationModule r
  mono_j : Mono A.rotationJ
  cokernel_j : IsGraphLineBundle (cokernel A.rotationJ) A.rotationPole

/-- Assemble the rank result with the known graph-base-change facts. -/
theorem rotationConditionsOfBundle (A : Shtuka p X S r)
    (bundle : IsVectorBundle A.rotationModule r) (P : A.PullbackConditions) :
    A.RotationConditions := by
  refine ⟨bundle, ?_, A.rotationJ_cokernel P⟩
  have := P.mono
  infer_instance

/-- Once the displayed geometric facts are supplied, the shtuka is complete. -/
def rotate (A : Shtuka p X S r) (h : A.RotationConditions) :
    Shtuka p X S r where
  E := A.E'
  E' := A.rotationModule
  bundle_E := A.bundle_E'
  bundle_E' := h.bundle
  j := A.rotationJ
  t := A.rotationT
  mono_j := h.mono_j
  mono_t := inferInstance
  pole := A.rotationPole
  zero := A.zero
  cokernel_j := h.cokernel_j
  cokernel_t := A.rotationT_cokernel

/-- The map on the new second bundle is forced by the pushout functor. -/
def rotationMap {A B : Shtuka p X S r} (a : A ⟶ B) :
    A.rotationModule ⟶ B.rotationModule :=
  pushout.map A.t ((Scheme.Modules.pullback (twist p X S)).map A.j)
    B.t ((Scheme.Modules.pullback (twist p X S)).map B.j)
    a.hom' ((Scheme.Modules.pullback (twist p X S)).map a.hom')
    ((Scheme.Modules.pullback (twist p X S)).map a.hom)
    a.t_comp (by
      rw [← Functor.map_comp, a.j_comp, Functor.map_comp])

@[reassoc]
theorem rotationJ_map {A B : Shtuka p X S r} (a : A ⟶ B) :
    A.rotationJ ≫ rotationMap a = a.hom' ≫ B.rotationJ :=
  pushout.inl_desc _ _ _

@[reassoc]
theorem rotationT_map {A B : Shtuka p X S r} (a : A ⟶ B) :
    A.rotationT ≫ rotationMap a =
      (Scheme.Modules.pullback (twist p X S)).map a.hom' ≫ B.rotationT :=
  pushout.inr_desc _ _ _

@[simp]
theorem rotationMap_id (A : Shtuka p X S r) :
    rotationMap (𝟙 A) = 𝟙 A.rotationModule := by
  apply pushout.hom_ext
  · simp only [rotationJ_map, id_hom', Category.id_comp, Category.comp_id]
  · simp only [rotationT_map, id_hom', Category.comp_id]
    rw [(Scheme.Modules.pullback (twist p X S)).map_id, Category.id_comp]

@[reassoc]
theorem rotationMap_comp {A B C : Shtuka p X S r}
    (a : A ⟶ B) (b : B ⟶ C) :
    rotationMap (a ≫ b) = rotationMap a ≫ rotationMap b := by
  apply pushout.hom_ext
  · simp only [rotationJ_map, Category.assoc, rotationJ_map_assoc,
      comp_hom']
  · simp only [rotationT_map, Category.assoc, rotationT_map_assoc,
      comp_hom', Functor.map_comp]

/-- The map on the candidate shtuka is the fixed pushout map. -/
def rotateHom {A B : Shtuka p X S r} (a : A ⟶ B)
    (hA : A.RotationConditions) (hB : B.RotationConditions) :
    A.rotate hA ⟶ B.rotate hB where
  hom := a.hom'
  hom' := rotationMap a
  pole_eq := by
    change A.pole ≫ primeFieldFrobenius p X =
      B.pole ≫ primeFieldFrobenius p X
    exact congrArg (· ≫ primeFieldFrobenius p X) a.pole_eq
  zero_eq := a.zero_eq
  j_comp := rotationJ_map a
  t_comp := rotationT_map a

end Shtuka

end MathlibExt.AlgebraicGeometry.ShtukaPartialFrobenius
