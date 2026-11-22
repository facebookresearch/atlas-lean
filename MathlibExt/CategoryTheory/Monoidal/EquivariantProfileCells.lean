/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Limits.Shapes.NaturalArrowColimit
public import MathlibExt.CategoryTheory.Action.Arrow
public import MathlibExt.CategoryTheory.Action.ArrowTensor
public import MathlibExt.CategoryTheory.Action.Orbit
public import MathlibExt.CategoryTheory.Monoidal.FiniteCube
public import MathlibExt.CategoryTheory.Operad.Colored.Profile
public import Mathlib.CategoryTheory.Action.Monoidal
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.Data.Fintype.Powerset

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Equiv.Sigma

/-!
# Positive heterogeneous equivariant pushout-product cells

Every original finite profile, proper face, group action, tensor coefficient,
source and target orbit cocone is retained. Positive-family generators range
over all finite multiplicity tuples and arbitrary equivariant coefficients.
The unary unit normalization imposes no cofibrancy condition on the unit.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CategoryTheory.OperadicOrbitCells.ProfileGeometry

open CategoryTheory Limits MonoidalCategory Operad
open scoped MonoidalCategory


section source_InitialAttachment_MarkedBoundary_slice_0
universe uc u v us
open CategoryTheory Limits MonoidalCategory Operad
attribute [local instance] FintypeCat.fintype
variable {W : Type uc}
/-- One original input color and its original X/X′ cube coordinate. -/
abbrev MarkedColor (W : Type uc) := FiniteCube.Index 1 × Discrete W

/-- All actual finite marked heterogeneous input families, with their original
input bijections and original coordinate face maps. -/
abbrev MarkedInputs (W : Type uc) := FiniteFamily (MarkedColor W)

instance markedColorHomSubsingleton (P Q : MarkedColor W) : Subsingleton (P ⟶ Q) :=
  inferInstanceAs (Subsingleton ((P.1 ⟶ Q.1) × (P.2 ⟶ Q.2)))
end source_InitialAttachment_MarkedBoundary_slice_0

section source_InitialAttachment_MarkedBoundary_slice_1
universe uc u v us
open CategoryTheory Limits MonoidalCategory Operad
attribute [local instance] FintypeCat.fintype
variable {W : Type uc}
/-- Marked input morphisms are determined by their original input bijection:
their remaining coordinates lie in the actual thin cube/color category. -/
theorem markedHom_ext {P Q : MarkedInputs W} {f g : P ⟶ Q} (he : f.equiv = g.equiv) :
    f = g := by
  rcases f with ⟨ef, hf⟩
  rcases g with ⟨eg, hg⟩
  cases he
  exact FiniteFamily.Hom_ext
    (f := { equiv := ef, hom := hf }) (g := { equiv := ef, hom := hg }) rfl
    (fun i => heq_of_eq (Subsingleton.elim (hf i) (hg i)))
end source_InitialAttachment_MarkedBoundary_slice_1

section source_PiFamilyAndCarrier
universe uc u v
variable {W : Type uc} {C : Type u} [Category.{v} C]

/-- The actual original indexed family forms its original discrete diagram. -/
def piFamilyFunctor : (W → C) ⥤ Discrete W ⥤ C where
  obj X := Discrete.functor X
  map f := Discrete.natTrans (fun i => f i.as)
  map_id _ := by ext i; rfl
  map_comp _ _ := by ext i; rfl

/-- Evaluate the original arrow family at its actual one-slot marked coordinate. -/
def markedInputCarrier {X Xprime : W → C} (x : X ⟶ Xprime) : MarkedColor W ⥤ C :=
  Functor.uncurry.obj (FiniteCube.coordinateCube (C := W → C) x (0 : Fin 1) ⋙
    piFamilyFunctor)
end source_PiFamilyAndCarrier

section source_InitialAttachment_MarkedContraction_slice_3
universe uc u v
variable {W : Type uc} {C : Type u} [Category.{v} C]
/-- The top one-slot coordinate is precisely the original X′ component. -/
theorem markedCarrier_top {X Xprime : W → C} (x : X ⟶ Xprime) (r : W) :
    (markedInputCarrier x).obj (Finset.univ, Discrete.mk r) = Xprime r := by
  change (if (0 : Fin 1) ∈ (Finset.univ : FiniteCube.Index 1) then Xprime else X) r = Xprime r
  rw [ite_eq_left (Finset.mem_univ _)]

/-- Every non-top one-slot coordinate is precisely the original X component. -/
theorem markedCarrier_old {X Xprime : W → C} (x : X ⟶ Xprime)
    (s : FiniteCube.Index 1) (hs : s ≠ Finset.univ) (r : W) :
    (markedInputCarrier x).obj (s, Discrete.mk r) = X r := by
  have he : s = ∅ := congrArg Subtype.val (FiniteCube.puncturedOne_eq_empty ⟨s, hs⟩)
  change (if (0 : Fin 1) ∈ s then Xprime else X) r = X r
  rw [he, ite_eq_right (Finset.notMem_empty _)]
end source_InitialAttachment_MarkedContraction_slice_3

section source_InitialAttachment_ProfileCells_slice_4
universe uc u v us
open CategoryTheory Limits MonoidalCategory Operad
attribute [local instance] FintypeCat.fintype
variable {W : Type uc}
variable {C : Type u} [Category.{v} C]
/-- The degree of the actual displayed finite colored profile. -/
def inputCount (P : ColoredProfile W) : ℕ := Fintype.card P.inputs

/-- The original displayed profile is enumerated solely to use the shared
ordered heterogeneous cube; its original colors and every input are retained. -/
def inputEnumeration (P : ColoredProfile W) : Fin (inputCount P) ≃ P.inputs :=
  (Fintype.equivFin P.inputs).symm

/-- The actual component of the original color-indexed arrow at every original
finite profile input. -/
def profileArrowFamily {X Xprime : W → C} (x : X ⟶ Xprime) (P : ColoredProfile W) :
    ∀ i : Fin (inputCount P),
      X (P.inputColor (inputEnumeration P i)) ⟶ Xprime (P.inputColor (inputEnumeration P i)) :=
  fun i => x (P.inputColor (inputEnumeration P i))
end source_InitialAttachment_ProfileCells_slice_4

section source_InitialAttachment_ProfileSymmetry
universe uc


open CategoryTheory

attribute [local instance] FintypeCat.fintype

variable {W : Type uc}

/-- The actual original input fiber at an original color. -/
abbrev ColorFiber (P : ColoredProfile W) (r : W) := {i : P.inputs // P.inputColor i = r}

/-- Original input positions decompose over their actual original colors. -/
def inputColorFiberEquiv (P : ColoredProfile W) : P.inputs ≃ Σ r : W, ColorFiber P r where
  toFun i := ⟨P.inputColor i, ⟨i, rfl⟩⟩
  invFun i := i.2.1
  left_inv _ := rfl
  right_inv i := by
    rcases i with ⟨r, i, hi⟩
    cases hi
    rfl

/-- The actual original profile automorphism restricts to every original color
fiber, retaining its original input permutation. -/
def profileAutFiberPermutation (P : ColoredProfile W) (f : Aut P) (r : W) :
    Equiv.Perm (ColorFiber P r) where
  toFun i := ⟨f.asIso.hom.inputEquiv i.1, (f.asIso.hom.inputColor_eq i.1).symm.trans i.2⟩
  invFun i := ⟨f.asIso.hom.inputEquiv.symm i.1,
    (f.asIso.hom.inputColor_eq (f.asIso.hom.inputEquiv.symm i.1)).trans
      ((congrArg P.inputColor (f.asIso.hom.inputEquiv.apply_symm_apply i.1)).trans i.2)⟩
  left_inv i := Subtype.ext (f.asIso.hom.inputEquiv.symm_apply_apply i.1)
  right_inv i := Subtype.ext (f.asIso.hom.inputEquiv.apply_symm_apply i.1)

/-- The original global input permutation assembled from arbitrary original
fiber permutations uses exactly the actual input/color decomposition. -/
def fiberInputPermutation (P : ColoredProfile W) (f : ∀ r : W, Equiv.Perm (ColorFiber P r)) :
    Equiv.Perm P.inputs :=
  (inputColorFiberEquiv P).trans (Equiv.sigmaCongrRight f) |>.trans (inputColorFiberEquiv P).symm

theorem fiberInputPermutation_color (P : ColoredProfile W)
    (f : ∀ r : W, Equiv.Perm (ColorFiber P r)) (i : P.inputs) :
    P.inputColor (fiberInputPermutation P f i) = P.inputColor i :=
  (f (P.inputColor i) ⟨i, rfl⟩).2

/-- Reassemble the actual original colored profile automorphism from all its
original color-fiber permutations, retaining its original output color. -/
def fiberProfileAut (P : ColoredProfile W) (f : ∀ r : W, Equiv.Perm (ColorFiber P r)) : Aut P :=
  Aut.of (asIso (show P ⟶ P from
    { inputEquiv := fiberInputPermutation P f
      inputColor_eq i := (fiberInputPermutation_color P f i).symm
      outputColor_eq := rfl }))

/-- The actual original profile automorphism group is the product of the
permutation groups of all its actual original color fibers. -/
def profileAutFiberMulEquiv (P : ColoredProfile W) :
    Aut P ≃* ∀ r : W, Equiv.Perm (ColorFiber P r) where
  toFun f := profileAutFiberPermutation P f
  invFun f := fiberProfileAut P f
  left_inv f := by
    apply Aut.ext
    apply Iso.ext
    apply ColoredProfile.Hom.ext
    apply Equiv.ext
    intro i
    rfl
  right_inv f := by
    funext r
    apply Equiv.ext
    rintro ⟨i, hi⟩
    apply Subtype.ext
    cases hi
    rfl
  map_mul' f g := by
    funext r
    apply Equiv.ext
    intro i
    apply Subtype.ext
    rfl

/-- The original multiplicity at each original color. -/
def colorMultiplicity (P : ColoredProfile W) (r : W) : ℕ := by
  classical
  exact Fintype.card (ColorFiber P r)

/-- Enumerating one original finite color fiber transports its actual
permutation group to the symmetric group of its original multiplicity. -/
def colorFiberSigmaMulEquiv (P : ColoredProfile W) (r : W) :
    Equiv.Perm (ColorFiber P r) ≃* Equiv.Perm (Fin (colorMultiplicity P r)) := by
  classical
  let e : ColorFiber P r ≃ Fin (colorMultiplicity P r) := Fintype.equivFin _
  exact
    { e.permCongr with
      map_mul' := fun f g => (e.permCongr_trans g f).symm }

/-- The same original full automorphism group is the displayed product of
symmetric groups of the actual original color multiplicities. -/
def profileAutSigmaMulEquiv (P : ColoredProfile W) :
    Aut P ≃* ∀ r : W, Equiv.Perm (Fin (colorMultiplicity P r)) :=
  (profileAutFiberMulEquiv P).trans
    { toFun f := fun r => colorFiberSigmaMulEquiv P r (f r)
      invFun f := fun r => (colorFiberSigmaMulEquiv P r).symm (f r)
      left_inv f := funext (fun r => (colorFiberSigmaMulEquiv P r).symm_apply_apply (f r))
      right_inv f := funext (fun r => (colorFiberSigmaMulEquiv P r).apply_symm_apply (f r))
      map_mul' f g := funext (fun r => (colorFiberSigmaMulEquiv P r).map_mul (f r) (g r)) }
end source_InitialAttachment_ProfileSymmetry

section source_InitialAttachment_ProfileAction_Pure
universe uc us


open CategoryTheory Limits MonoidalCategory

variable {W : Type uc}

/-- The original full finite profile with each original input at X′. -/
def topMarkedProfile (P : ColoredProfile W) : MarkedInputs W where
  index := P.inputs
  obj i := (Finset.univ, Discrete.mk (P.inputColor i))

/-- The actual original profile automorphism acts on its original top input
family by its same original input bijection and original color equalities. -/
def profileAutTopIso (P : ColoredProfile W) (f : Aut P) : topMarkedProfile P ≅ topMarkedProfile P :=
  FiniteFamily.isoOfComponents f.asIso.hom.inputEquiv
    (fun i => eqToIso (congrArg
      (fun r : W => ((Finset.univ : FiniteCube.Index 1), Discrete.mk r))
      (f.asIso.hom.inputColor_eq i)))

/-- These are the actual original automorphism group action maps, with
identity and multiplication proved in the original marked input category. -/
def profileAutTopHom (P : ColoredProfile W) : Aut P →* Aut (topMarkedProfile P) where
  toFun f := Aut.of (profileAutTopIso P f)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply markedHom_ext
    rfl
  map_mul' f g := by
    apply Aut.ext
    apply Iso.ext
    apply markedHom_ext
    rfl

/-- The original full colored profile automorphism group is source-small,
using only its actual finite input permutation and no shrinking of W. -/
instance profileAutSmall (P : ColoredProfile W) : Small.{us} (Aut P) := by
  apply small_of_injective.{us} (f := fun f : Aut P => f.asIso.hom.inputEquiv)
  intro f g h
  apply Aut.ext
  apply Iso.ext
  exact ColoredProfile.Hom.ext h

instance profileSingleAutLocallySmall (P : ColoredProfile W) :
    LocallySmall.{us} (SingleObj (Aut P)) where
  hom_small _ _ := inferInstanceAs (Small.{us} (Aut P))

instance profileSingleAutEssentiallySmall (P : ColoredProfile W) :
    EssentiallySmall.{us} (SingleObj (Aut P)) :=
  essentiallySmall_of_small_of_locallySmall _
end source_InitialAttachment_ProfileAction_Pure

section source_InitialAttachment_InputCube
universe uc u v us


open CategoryTheory Limits MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {W : Type uc}

/-- The original finite input set has its classical decidable equality. -/
local instance originalInputDecidableEq (P : ColoredProfile W) : DecidableEq P.inputs :=
  Classical.decEq _

/-- The actual subsets of the original finite input set. -/
abbrev ProfileInputSets (P : ColoredProfile W) := Finset P.inputs

/-- The actual proper subsets of the original finite input set. -/
abbrev ProfilePuncturedInputSets (P : ColoredProfile W) :=
  {S : ProfileInputSets P // S ≠ Finset.univ}

/-- The original input uses its target exactly when its position is selected. -/
def inputCoordinate (P : ColoredProfile W) (S : ProfileInputSets P) (i : P.inputs) :
    FiniteCube.Index 1 := if i ∈ S then Finset.univ else ∅

theorem inputCoordinate_mono (P : ColoredProfile W) {S T : ProfileInputSets P}
    (h : S ⊆ T) (i : P.inputs) : inputCoordinate P S i ⊆ inputCoordinate P T i := by
  by_cases hi : i ∈ S
  · have ht := h hi
    rw [inputCoordinate, inputCoordinate, ite_eq_left hi, ite_eq_left ht]
  · rw [inputCoordinate, ite_eq_right hi]
    exact Finset.empty_subset _

/-- The original finite input set cube, retaining every original position and
original color without choosing another input ordering. -/
def originalInputCube (P : ColoredProfile W) : ProfileInputSets P ⥤ MarkedInputs W where
  obj S := ⟨P.inputs, fun i => (inputCoordinate P S i, Discrete.mk (P.inputColor i))⟩
  map f :=
    { equiv := Equiv.refl P.inputs
      hom i := (homOfLE (inputCoordinate_mono P (leOfHom f) i), 𝟙 (Discrete.mk (P.inputColor i))) }
  map_id _ := markedHom_ext rfl
  map_comp _ _ := markedHom_ext rfl

/-- Include the original proper subsets into the full original subset cube. -/
def originalPuncturedInclusion (P : ColoredProfile W) :
    ProfilePuncturedInputSets P ⥤ ProfileInputSets P where
  obj S := S.1
  map f := homOfLE (leOfHom f)

/-- Carry each original selected position through its actual profile permutation. -/
def profileAutSubset (P : ColoredProfile W) (f : Aut P) (S : ProfileInputSets P) :
    ProfileInputSets P := S.map f.asIso.hom.inputEquiv.toEmbedding

theorem profileAutSubset_mem (P : ColoredProfile W) (f : Aut P) (S : ProfileInputSets P) (i : P.inputs) :
    f.asIso.hom.inputEquiv i ∈ profileAutSubset P f S ↔ i ∈ S := by
  simp only [profileAutSubset, Finset.mem_map_equiv, Equiv.symm_apply_apply]

theorem profileAutSubset_mono (P : ColoredProfile W) (f : Aut P) {S T : ProfileInputSets P}
    (h : S ⊆ T) : profileAutSubset P f S ⊆ profileAutSubset P f T :=
  Finset.map_subset_map.mpr h

/-- The actual profile permutation preserves all original subset inclusions. -/
def profileAutSubsetFunctor (P : ColoredProfile W) (f : Aut P) :
    ProfileInputSets P ⥤ ProfileInputSets P :=
  (show Monotone (profileAutSubset P f) from fun _ _ h => profileAutSubset_mono P f h).functor

theorem profileAutSubset_univ (P : ColoredProfile W) (f : Aut P) :
    profileAutSubset P f Finset.univ = Finset.univ := by
  apply Finset.ext
  intro i
  simp only [profileAutSubset, Finset.mem_map_equiv, Finset.mem_univ]

theorem profileAutSubset_punctured (P : ColoredProfile W) (f : Aut P)
    (S : ProfilePuncturedInputSets P) : profileAutSubset P f S.1 ≠ Finset.univ := by
  intro h
  apply S.2
  apply Finset.eq_univ_iff_forall.mpr
  intro i
  exact (profileAutSubset_mem P f S.1 i).mp (h.symm ▸ Finset.mem_univ _)

/-- The actual profile permutation preserves the original proper subsets. -/
def profileAutPunctured (P : ColoredProfile W) (f : Aut P) :
    ProfilePuncturedInputSets P ⥤ ProfilePuncturedInputSets P where
  obj S := ⟨profileAutSubset P f S.1, profileAutSubset_punctured P f S⟩
  map h := homOfLE (profileAutSubset_mono P f (leOfHom h))

/-- Every original profile automorphism carries each original cube coordinate
to its same original relabelled coordinate and preserves its original color. -/
def profileAutInputVertexIso (P : ColoredProfile W) (f : Aut P) (S : ProfileInputSets P) :
    (originalInputCube P).obj S ≅ (originalInputCube P).obj (profileAutSubset P f S) :=
  FiniteFamily.isoOfComponents f.asIso.hom.inputEquiv (fun i => eqToIso (Prod.ext
    (by
      change P.inputs at i
      change inputCoordinate P S i =
        inputCoordinate P (profileAutSubset P f S) (f.asIso.hom.inputEquiv i)
      simp only [inputCoordinate, profileAutSubset, Finset.mem_map_equiv]
      exact (congrArg (fun j : P.inputs => if j ∈ S then (Finset.univ : FiniteCube.Index 1) else ∅)
        (f.asIso.hom.inputEquiv.symm_apply_apply i)).symm)
    (congrArg Discrete.mk (f.asIso.hom.inputColor_eq i))))

/-- The actual original automorphism coordinate maps commute with every
original cube face, before applying the original coefficient tensor. -/
theorem profileAutInputVertexIso_face (P : ColoredProfile W) (f : Aut P)
    {S T : ProfileInputSets P} (h : S ⟶ T) :
    (originalInputCube P).map h ≫ (profileAutInputVertexIso P f T).hom =
      (profileAutInputVertexIso P f S).hom ≫
        (originalInputCube P).map ((profileAutSubsetFunctor P f).map h) :=
  markedHom_ext rfl

theorem profileAutSubset_one (P : ColoredProfile W) (S : ProfileInputSets P) :
    profileAutSubset P 1 S = S := by
  apply Finset.ext
  intro i
  simp only [profileAutSubset, Finset.mem_map_equiv]
  rfl

theorem profileAutSubset_mul (P : ColoredProfile W) (f g : Aut P) (S : ProfileInputSets P) :
    profileAutSubset P (f * g) S = profileAutSubset P f (profileAutSubset P g S) := by
  apply Finset.ext
  intro i
  simp only [profileAutSubset, Finset.mem_map_equiv]
  rfl

theorem profileAutInputVertexIso_one (P : ColoredProfile W) (S : ProfileInputSets P) :
    (profileAutInputVertexIso P 1 S).hom =
      (originalInputCube P).map (eqToHom (profileAutSubset_one P S).symm) :=
  markedHom_ext rfl

theorem profileAutInputVertexIso_mul (P : ColoredProfile W) (f g : Aut P) (S : ProfileInputSets P) :
    (profileAutInputVertexIso P g S).hom ≫
        (profileAutInputVertexIso P f (profileAutSubset P g S)).hom =
      (profileAutInputVertexIso P (f * g) S).hom ≫
        (originalInputCube P).map (eqToHom (profileAutSubset_mul P f g S)) :=
  markedHom_ext rfl
end source_InitialAttachment_InputCube

section source_InitialAttachment_InputBoundaryGeometry
universe uc u v us


open CategoryTheory Limits MonoidalCategory

variable {W : Type uc} {C : Type u} [Category.{v} C]
variable [HasColimitsOfSize.{us, us} C]

local instance boundaryActionSmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

/-- Apply the full source diagram to the original input-set cube. -/
def geometryInputTensorCube (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) : ProfileInputSets P ⥤ C :=
  originalInputCube P ⋙ D

/-- Restrict the actual input-set diagram to all original proper faces. -/
def geometryPuncturedTensor (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) : ProfilePuncturedInputSets P ⥤ C :=
  originalPuncturedInclusion P ⋙ geometryInputTensorCube D P

/-- The boundary is the actual original proper-face colimit. -/
def geometryInputBoundary (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) : C := colimit (geometryPuncturedTensor D P)

/-- Every original automorphism acts on each proper original input set and
its actual original coefficient/input tensor before the boundary quotient. -/
def geometryAutCocone (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) (g : Aut P) :
    Cocone (geometryPuncturedTensor D P) where
  pt := geometryInputBoundary D P
  ι.app S := (D).map (profileAutInputVertexIso P g S.1).hom ≫
    colimit.ι (geometryPuncturedTensor D P) ((profileAutPunctured P g).obj S)
  ι.naturality S T h := by
    let q := (originalPuncturedInclusion P).map h
    let k := (profileAutSubsetFunctor P g).map q
    have hs : D.map ((originalInputCube P).map q) ≫ D.map (profileAutInputVertexIso P g T.1).hom =
        D.map (profileAutInputVertexIso P g S.1).hom ≫ D.map ((originalInputCube P).map k) :=
      (D.map_comp _ _).symm.trans
        ((congrArg D.map (profileAutInputVertexIso_face P g q)).trans (D.map_comp _ _))
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ colimit.ι (geometryPuncturedTensor D P) ((profileAutPunctured P g).obj T)) hs).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (D.map (profileAutInputVertexIso P g S.1).hom ≫ ·)
            (colimit.w (geometryPuncturedTensor D P) ((profileAutPunctured P g).map h))).trans
              (Category.comp_id _).symm)))

/-- The original automorphism boundary map is constructed from all the
original relabelled proper faces by the actual boundary colimit. -/
def geometryAutMap (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) (g : Aut P) :
    geometryInputBoundary D P ⟶ geometryInputBoundary D P :=
  colimit.desc _ (geometryAutCocone D P g)

theorem geometryAutMap_face (D : MarkedInputs W ⥤ C) (P : ColoredProfile W)
    (g : Aut P) (S : ProfilePuncturedInputSets P) :
    colimit.ι (geometryPuncturedTensor D P) S ≫ geometryAutMap D P g =
      (D).map (profileAutInputVertexIso P g S.1).hom ≫
        colimit.ι (geometryPuncturedTensor D P) ((profileAutPunctured P g).obj S) :=
  colimit.ι_desc _ _

theorem geometryAutMap_one (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) :
    geometryAutMap D P 1 = 𝟙 (geometryInputBoundary D P) := by
  let B := geometryPuncturedTensor D P
  apply colimit.hom_ext
  intro S
  let e : S = (profileAutPunctured P 1).obj S := Subtype.ext (profileAutSubset_one P S.1).symm
  let f := eqToHom e
  have hf : (originalPuncturedInclusion P).map f = eqToHom (profileAutSubset_one P S.1).symm :=
    Subsingleton.elim _ _
  have hm : D.map (profileAutInputVertexIso P 1 S.1).hom = B.map f :=
    (congrArg D.map (profileAutInputVertexIso_one P S.1)).trans
      (congrArg (fun k => D.map ((originalInputCube P).map k)) hf).symm
  exact (geometryAutMap_face D P 1 S).trans
    ((congrArg (· ≫ colimit.ι B ((profileAutPunctured P 1).obj S)) hm).trans
      ((colimit.w B f).trans (Category.comp_id _).symm))

private theorem pairEvaluation {D : Type*} [Category* D] {U V Z W X Y : D}
    (m : U ⟶ V) (b : V ⟶ Z) (c : Z ⟶ W) (p : U ⟶ X) (j : X ⟶ Z)
    (q : X ⟶ Y) (k : Y ⟶ W) (h₁ : m ≫ b = p ≫ j) (h₂ : j ≫ c = q ≫ k) :
    m ≫ (b ≫ c) = (p ≫ q) ≫ k :=
  (Category.assoc m b c).symm.trans
    ((congrArg (· ≫ c) h₁).trans
      ((Category.assoc p j c).trans
        ((congrArg (p ≫ ·) h₂).trans (Category.assoc p q k).symm)))

/-- Composition of the actual original boundary action maps is the original
profile automorphism multiplication, with every original input permutation. -/
theorem geometryAutMap_mul (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) (f g : Aut P) :
    geometryAutMap D P (f * g) = geometryAutMap D P g ≫ geometryAutMap D P f := by
  let B := geometryPuncturedTensor D P
  apply colimit.hom_ext
  intro S
  let Sg : ProfilePuncturedInputSets P := (profileAutPunctured P g).obj S
  let Sfg : ProfilePuncturedInputSets P := (profileAutPunctured P (f * g)).obj S
  let Sf_g : ProfilePuncturedInputSets P := (profileAutPunctured P f).obj Sg
  let e : Sfg = Sf_g := Subtype.ext (profileAutSubset_mul P f g S.1)
  let k : Sfg ⟶ Sf_g := eqToHom e
  have hk : (originalPuncturedInclusion P).map k = eqToHom (profileAutSubset_mul P f g S.1) :=
    Subsingleton.elim _ _
  have hv : D.map (profileAutInputVertexIso P g S.1).hom ≫
      D.map (profileAutInputVertexIso P f Sg.1).hom =
        D.map (profileAutInputVertexIso P (f * g) S.1).hom ≫ B.map k :=
    (D.map_comp _ _).symm.trans
      ((congrArg D.map (profileAutInputVertexIso_mul P f g S.1)).trans
        ((D.map_comp _ _).trans
          (congrArg (D.map (profileAutInputVertexIso P (f * g) S.1).hom ≫ ·)
            (congrArg (fun z => D.map ((originalInputCube P).map z)) hk).symm)))
  have heval : colimit.ι B S ≫ (geometryAutMap D P g ≫ geometryAutMap D P f) =
      (D.map (profileAutInputVertexIso P g S.1).hom ≫
        D.map (profileAutInputVertexIso P f Sg.1).hom) ≫ colimit.ι B Sf_g :=
    pairEvaluation (colimit.ι B S) (geometryAutMap D P g) (geometryAutMap D P f)
      (D.map (profileAutInputVertexIso P g S.1).hom) (colimit.ι B Sg)
      (D.map (profileAutInputVertexIso P f Sg.1).hom) (colimit.ι B Sf_g)
      (geometryAutMap_face D P g S) (geometryAutMap_face D P f Sg)
  have hright : colimit.ι B S ≫ (geometryAutMap D P g ≫ geometryAutMap D P f) =
      D.map (profileAutInputVertexIso P (f * g) S.1).hom ≫ colimit.ι B Sfg :=
    heval.trans ((congrArg (· ≫ colimit.ι B Sf_g) hv).trans
      ((Category.assoc (D.map (profileAutInputVertexIso P (f * g) S.1).hom)
        (B.map k) (colimit.ι B Sf_g)).trans
        (congrArg (D.map (profileAutInputVertexIso P (f * g) S.1).hom ≫ ·) (colimit.w B k))))
  exact (geometryAutMap_face D P (f * g) S).trans hright.symm

/-- The actual original profile group action on the full original punctured
tensor boundary is a genuine representation, not an assumed compatibility family. -/
def geometryBoundaryRepresentation (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) :
    Aut P →* End (geometryInputBoundary D P) where
  toFun g := End.of (geometryAutMap D P g)
  map_one' := End.ext (geometryAutMap_one D P)
  map_mul' f g := End.ext (geometryAutMap_mul D P f g)

/-- The constructed boundary representation gives its original group diagram. -/
def geometryBoundaryActionFunctor (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) : SingleObj (Aut P) ⥤ C :=
  SingleObj.functor (geometryBoundaryRepresentation D P)
end source_InitialAttachment_InputBoundaryGeometry

section source_InitialAttachment_InputTop_Pure
universe uc u v us


open CategoryTheory Limits MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {W : Type uc}

/-- The actual top input set is the original all-X′ marked profile, with
every original input position and original color retained. -/
def originalInputTopIso (P : ColoredProfile W) :
    (originalInputCube P).obj Finset.univ ≅ topMarkedProfile P :=
  FiniteFamily.isoOfComponents (Equiv.refl P.inputs) (fun i => eqToIso (Prod.ext
    (by
      change inputCoordinate P Finset.univ i = Finset.univ
      exact ite_eq_left (Finset.mem_univ i)) rfl))

/-- The original full-input permutation is an automorphism of the actual top vertex. -/
def originalInputTopDirectIso (P : ColoredProfile W) (g : Aut P) :
    (originalInputCube P).obj Finset.univ ≅ (originalInputCube P).obj Finset.univ :=
  profileAutInputVertexIso P g Finset.univ ≪≫
    (originalInputCube P).mapIso (eqToIso (profileAutSubset_univ P g))

theorem originalInputTopDirectIso_eq (P : ColoredProfile W) (g : Aut P) :
    originalInputTopDirectIso P g =
      originalInputTopIso P ≪≫ profileAutTopIso P g ≪≫ (originalInputTopIso P).symm := by
  apply Iso.ext
  apply markedHom_ext
  apply Equiv.ext
  intro i
  rfl

/-- The actual original input-set top action is the same original profile
automorphism action transported through the original top-profile comparison. -/
def originalInputTopHom (P : ColoredProfile W) : Aut P →* Aut ((originalInputCube P).obj Finset.univ) :=
  (Aut.autMulEquivOfIso (originalInputTopIso P).symm).toMonoidHom.comp (profileAutTopHom P)

section Geometry

variable {C : Type u} [Category.{v} C]

/-- Tensor the original full-input automorphism through the actual source diagram. -/
def geometryInputTopRepresentation (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) :
    Aut P →* End (D.obj ((originalInputCube P).obj Finset.univ)) :=
  Aut.toEnd.comp
    ((Functor.mapAut ((originalInputCube P).obj Finset.univ) D).comp (originalInputTopHom P))

theorem geometryInputTopRepresentation_hom (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) (g : Aut P) :
    (geometryInputTopRepresentation D P g).asHom =
      D.map (profileAutInputVertexIso P g Finset.univ).hom ≫
        D.map ((originalInputCube P).map (eqToHom (profileAutSubset_univ P g))) := by
  have hi : (originalInputTopHom P g).asIso = originalInputTopDirectIso P g :=
    (originalInputTopDirectIso_eq P g).symm
  exact (congrArg (fun e => D.map e.hom) hi).trans (D.map_comp _ _)

end Geometry
end source_InitialAttachment_InputTop_Pure

section source_InitialAttachment_InputArrowGeometry
universe uc u v us


open CategoryTheory Limits MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {W : Type uc} {C : Type u} [Category.{v} C] [HasColimitsOfSize.{us, us} C]

local instance inputArrowSmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

/-- Every original proper face maps to the actual full top vertex. -/
def geometryInputTopCocone (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) :
    Cocone (geometryPuncturedTensor D P) where
  pt := (geometryInputTensorCube D P).obj Finset.univ
  ι.app S := (geometryInputTensorCube D P).map (homOfLE (Finset.subset_univ S.1))
  ι.naturality S T h := by
    let F := geometryInputTensorCube D P
    let q := (originalPuncturedInclusion P).map h
    let t : T.1 ⟶ (Finset.univ : ProfileInputSets P) := homOfLE (Finset.subset_univ T.1)
    let s : S.1 ⟶ (Finset.univ : ProfileInputSets P) := homOfLE (Finset.subset_univ S.1)
    exact (F.map_comp q t).symm.trans
      ((congrArg F.map (Subsingleton.elim (q ≫ t) s)).trans (Category.comp_id _).symm)

/-- The original proper-face cocone induces the actual boundary-to-top map. -/
def geometryBoundaryToTop (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) :
    geometryInputBoundary D P ⟶ (geometryInputTensorCube D P).obj Finset.univ :=
  colimit.desc _ (geometryInputTopCocone D P)

theorem geometryBoundaryToTop_face (D : MarkedInputs W ⥤ C) (P : ColoredProfile W)
    (S : ProfilePuncturedInputSets P) :
    colimit.ι (geometryPuncturedTensor D P) S ≫ geometryBoundaryToTop D P =
      (geometryInputTensorCube D P).map (homOfLE (Finset.subset_univ S.1)) :=
  colimit.ι_desc _ _

/-- Every original profile automorphism preserves the original full
boundary-to-top arrow; its source and target actions are both constructed. -/
theorem geometryBoundaryToTop_equivariance (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) (g : Aut P) :
    geometryAutMap D P g ≫ geometryBoundaryToTop D P =
      geometryBoundaryToTop D P ≫ (geometryInputTopRepresentation D P g).asHom := by
  let F := geometryInputTensorCube D P
  let B := geometryPuncturedTensor D P
  apply colimit.hom_ext
  intro S
  let Sg := (profileAutPunctured P g).obj S
  let q : S.1 ⟶ (Finset.univ : ProfileInputSets P) := homOfLE (Finset.subset_univ S.1)
  let r := (profileAutSubsetFunctor P g).map q
  let e : profileAutSubset P g Finset.univ ⟶ (Finset.univ : ProfileInputSets P) :=
    eqToHom (profileAutSubset_univ P g)
  let t : Sg.1 ⟶ (Finset.univ : ProfileInputSets P) := homOfLE (Finset.subset_univ Sg.1)
  have hs : F.map q ≫ D.map (profileAutInputVertexIso P g Finset.univ).hom =
      D.map (profileAutInputVertexIso P g S.1).hom ≫ F.map r :=
    (D.map_comp _ _).symm.trans
      ((congrArg D.map (profileAutInputVertexIso_face P g q)).trans (D.map_comp _ _))
  have he : F.map r ≫ F.map e = F.map t :=
    (F.map_comp r e).symm.trans (congrArg F.map (Subsingleton.elim (r ≫ e) t))
  have hn : F.map q ≫ (geometryInputTopRepresentation D P g).asHom =
      D.map (profileAutInputVertexIso P g S.1).hom ≫ F.map t :=
    (congrArg (F.map q ≫ ·) (geometryInputTopRepresentation_hom D P g)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ F.map e) hs).trans
          ((Category.assoc _ _ _).trans
            (congrArg (D.map (profileAutInputVertexIso P g S.1).hom ≫ ·) he))))
  have hl : colimit.ι B S ≫ (geometryAutMap D P g ≫ geometryBoundaryToTop D P) =
      D.map (profileAutInputVertexIso P g S.1).hom ≫ F.map t :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ geometryBoundaryToTop D P) (geometryAutMap_face D P g S)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (D.map (profileAutInputVertexIso P g S.1).hom ≫ ·)
            (geometryBoundaryToTop_face D P Sg))))
  have hr : colimit.ι B S ≫
      (geometryBoundaryToTop D P ≫ (geometryInputTopRepresentation D P g).asHom) =
        D.map (profileAutInputVertexIso P g S.1).hom ≫ F.map t :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (geometryInputTopRepresentation D P g).asHom)
        (geometryBoundaryToTop_face D P S)).trans hn)
  exact hl.trans hr.symm

/-- The constructed top representation gives its original group diagram. -/
def geometryInputTopActionFunctor (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) : SingleObj (Aut P) ⥤ C :=
  SingleObj.functor (geometryInputTopRepresentation D P)

/-- The original full attaching arrow is an actual equivariant natural
transformation for the original full profile automorphism group. -/
def geometryBoundaryTopTransformation (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) :
    geometryBoundaryActionFunctor D P ⟶ geometryInputTopActionFunctor D P :=
  SingleObj.natTrans (geometryBoundaryToTop D P)
    (fun g => geometryBoundaryToTop_equivariance D P g)

local instance inputArrowAutColimits (P : ColoredProfile W) : HasColimitsOfShape (SingleObj (Aut P)) C :=
  HasColimitsOfShape.of_essentiallySmall C _

/-- The original full equivariant attaching arrow is genuinely balanced over
the actual original profile group, with both orbit objects constructed. -/
def geometryBalancedProfileArrow (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) : Arrow C :=
  Arrow.mk (colimMap (geometryBoundaryTopTransformation D P))
end source_InitialAttachment_InputArrowGeometry

section source_InitialAttachment_CubeProfiles_Pure
universe uc u v


open CategoryTheory Limits MonoidalCategory

variable {W : Type uc}

/-- Every actual original profile input has its original color and original
domain-coordinate object in the one-slot marked cube. -/
def profileDomainMarks (P : ColoredProfile W) : Fin (inputCount P) → MarkedColor W :=
  fun i => (∅, Discrete.mk (P.inputColor (inputEnumeration P i)))

/-- Every original input retains its color and uses its target mark. -/
def profileTopMarks (P : ColoredProfile W) : Fin (inputCount P) → MarkedColor W :=
  fun i => (Finset.univ, Discrete.mk (P.inputColor (inputEnumeration P i)))

/-- Every actual original input has its original domain-to-top coordinate map. -/
def profileMarkedArrows (P : ColoredProfile W) :
    ∀ i : Fin (inputCount P), profileDomainMarks P i ⟶ profileTopMarks P i :=
  fun i => (homOfLE (Finset.empty_subset Finset.univ),
    𝟙 (Discrete.mk (P.inputColor (inputEnumeration P i))))

/-- The shared original finite family cube, interpreted as actual marked
colored profiles, with all heterogeneous original input colors retained. -/
def profileMarkedCube (P : ColoredProfile W) : FiniteCube.Index (inputCount P) ⥤ MarkedInputs W :=
  FiniteCube.familyCube (profileMarkedArrows P) ⋙
    FiniteFamily.fixedIndexFunctor (C := MarkedColor W) (FintypeCat.of (Fin (inputCount P)))

theorem profileMarkedCube_color (P : ColoredProfile W)
    (S : FiniteCube.Index (inputCount P)) (i : Fin (inputCount P)) :
    (((profileMarkedCube P).obj S).obj i).2.as = P.inputColor (inputEnumeration P i) := by
  change ((if i ∈ S then profileTopMarks P i else profileDomainMarks P i).2).as = _
  split <;> rfl

section Carrier

variable {C : Type u} [Category.{v} C]

/-- Every actual marked cube vertex evaluates to precisely its original
heterogeneous X/X′ coordinate object. -/
theorem profileMarkedCarrier_vertex {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (S : FiniteCube.Index (inputCount P)) (i : Fin (inputCount P)) :
    (markedInputCarrier x).obj (((profileMarkedCube P).obj S).obj i) =
      FiniteCube.vertexFamily
        (fun i => X (P.inputColor (inputEnumeration P i)))
        (fun i => Xprime (P.inputColor (inputEnumeration P i))) S i := by
  change (markedInputCarrier x).obj
      (if i ∈ S then profileTopMarks P i else profileDomainMarks P i) =
    (if i ∈ S then Xprime (P.inputColor (inputEnumeration P i))
      else X (P.inputColor (inputEnumeration P i)))
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi, ite_eq_left hi]
    exact markedCarrier_top x _
  · rw [ite_eq_right hi, ite_eq_right hi]
    exact markedCarrier_old x ∅ FiniteCube.puncturedOneEmpty.2 _



end Carrier
end source_InitialAttachment_CubeProfiles_Pure

section source_InitialAttachment_BinaryTensor_Ordered
universe u v


open CategoryTheory Limits MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The fixed-index comparisons use the canonical original symmetric finite tensor. -/
local instance binaryFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C

/-- The original component square is retained under an arbitrary original
finite input bijection and the actual symmetric ordered tensor. -/
theorem orderedMapEquivSquare {m n : ℕ} {X Xprime : Fin m → C} {Y Yprime : Fin n → C}
    (e : Fin m ≃ Fin n) (f : ∀ i, X i ⟶ Xprime i) (g : ∀ i, Y i ⟶ Yprime i)
    (k : ∀ i, X i ⟶ Y (e i)) (l : ∀ i, Xprime i ⟶ Yprime (e i))
    (h : ∀ i, f i ≫ l i = k i ≫ g (e i)) :
    OrderedTensor.map f ≫ OrderedTensor.mapEquiv e l =
      OrderedTensor.mapEquiv e k ≫ OrderedTensor.map g := by
  have hl := OrderedTensor.mapEquiv_comp (Equiv.refl (Fin m)) e f l
  have hr := OrderedTensor.mapEquiv_comp e (Equiv.refl (Fin n)) k g
  have hc : OrderedTensor.mapEquiv ((Equiv.refl (Fin m)).trans e) (fun i => f i ≫ l i) =
      OrderedTensor.mapEquiv (e.trans (Equiv.refl (Fin n))) (fun i => k i ≫ g (e i)) :=
    OrderedTensor.mapEquiv_congr rfl _ _ (fun i => heq_of_eq (h i))
  exact (congrArg (· ≫ OrderedTensor.mapEquiv e l) (OrderedTensor.mapEquiv_refl f)).symm.trans
    (hl.trans (hc.trans (hr.symm.trans
      (congrArg (OrderedTensor.mapEquiv e k ≫ ·) (OrderedTensor.mapEquiv_refl g)))))

/-- The actual finite tensor at an explicit finite ordered index is compared
with that original order using its actual original enumeration permutation. -/
def fixedToOrderedIso {n : ℕ} (X : Fin n → C) :
    (fixedIndexTensorFunctor (C := C) (FintypeCat.of (Fin n))).obj X ≅ OrderedTensor.obj X :=
  OrderedTensor.isoEquiv
    (OrderedTensor.enumeration ((FiniteFamily.fixedIndexFunctor (C := C) (FintypeCat.of (Fin n))).obj X))
    (fun _ => Iso.refl _)

/-- The fixed ordered comparison keeps every original component map. -/
theorem fixedToOrderedIso_naturality {n : ℕ} {X Y : Fin n → C} (f : ∀ i, X i ⟶ Y i) :
    (fixedIndexTensorFunctor (C := C) (FintypeCat.of (Fin n))).map f ≫ (fixedToOrderedIso Y).hom =
      (fixedToOrderedIso X).hom ≫ OrderedTensor.map f := by
  let I := FintypeCat.of (Fin n)
  let e := OrderedTensor.enumeration ((FiniteFamily.fixedIndexFunctor (C := C) I).obj X)
  have hmap : (fixedIndexTensorFunctor (C := C) I).map f =
      OrderedTensor.map (fun i => f (e i)) :=
    FiniteTensor.ofSymmetric_map_fixedIndex I f
  have hx : (fixedToOrderedIso X).hom = OrderedTensor.mapEquiv e (fun _ => 𝟙 _) :=
    OrderedTensor.isoEquiv_hom e _
  have hy : (fixedToOrderedIso Y).hom = OrderedTensor.mapEquiv e (fun _ => 𝟙 _) :=
    OrderedTensor.isoEquiv_hom e _
  have hs : OrderedTensor.map (fun i => f (e i)) ≫ OrderedTensor.mapEquiv e (fun _ => 𝟙 _) =
      OrderedTensor.mapEquiv e (fun _ => 𝟙 _) ≫ OrderedTensor.map f :=
    orderedMapEquivSquare e (fun i => f (e i)) f (fun _ => 𝟙 _) (fun _ => 𝟙 _)
      (fun i => (Category.comp_id _).trans (Category.id_comp _).symm)
  exact (congrArg (· ≫ (fixedToOrderedIso Y).hom) hmap).trans
    ((congrArg (OrderedTensor.map (fun i => f (e i)) ≫ ·) hy).trans
      (hs.trans (congrArg (· ≫ OrderedTensor.map f) hx).symm))
end source_InitialAttachment_BinaryTensor_Ordered

section source_InitialAttachment_CubeTensor_Pure
universe uc u v


open CategoryTheory Limits MonoidalCategory

variable {W : Type uc} {C : Type u} [Category.{v} C]

/-- The original shared heterogeneous tensor cube retains its original finite
input family before applying the actual original tensor. -/
def rawProfileLeafCube {X Xprime : W → C} (x : X ⟶ Xprime) (P : ColoredProfile W) :
    FiniteCube.Index (inputCount P) ⥤ FiniteFamily C :=
  FiniteCube.familyCube (profileArrowFamily x P) ⋙
    FiniteFamily.fixedIndexFunctor (C := C) (FintypeCat.of (Fin (inputCount P)))

/-- Every marked cube leaf is its actual original X/X′ leaf, with the original
finite ordered input position retained. -/
def profileMarkedLeafFamilyIso {X Xprime : W → C} (x : X ⟶ Xprime) (P : ColoredProfile W)
    (S : FiniteCube.Index (inputCount P)) :
    (FiniteFamily.map (markedInputCarrier x)).obj ((profileMarkedCube P).obj S) ≅
      (rawProfileLeafCube x P).obj S :=
  FiniteFamily.isoOfComponents (Equiv.refl (Fin (inputCount P)))
    (fun i => eqToIso (profileMarkedCarrier_vertex x P S i))

private theorem functorMapHEq {D : Type*} [Category* D] {E : Type*} [Category* E]
    (F : D ⥤ E) {A B A' B' : D} (f : A ⟶ B) (g : A' ⟶ B')
    (hA : A = A') (hB : B = B') (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hA
  cases hB
  exact heq_of_eq (congrArg F.map (eq_of_heq h))

private theorem squareOfHEq {D : Type*} [Category* D] {A B A' B' : D}
    (f : A ⟶ B) (g : A' ⟶ B') (hA : A = A') (hB : B = B') (h : HEq f g) :
    f ≫ eqToHom hB = eqToHom hA ≫ g := by
  have hf := (conj_eqToHom_iff_heq f g hA hB).mpr h
  rw [hf]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The original marked one-slot arrow evaluates to exactly the original
color component of x, retaining both original object transports. -/
theorem markedInputCarrier_arrow {X Xprime : W → C} (x : X ⟶ Xprime) (r : W) :
    HEq ((markedInputCarrier x).map
      (show (∅, Discrete.mk r) ⟶ (Finset.univ, Discrete.mk r) from
        (homOfLE (Finset.empty_subset Finset.univ), 𝟙 (Discrete.mk r)))) (x r) := by
  let M := FiniteCube.coordinateCube (C := W → C) x (0 : Fin 1)
  let f : (∅ : FiniteCube.Index 1) ⟶ Finset.univ := homOfLE (Finset.empty_subset Finset.univ)
  have hX : M.obj ∅ = X := by
    change (if (0 : Fin 1) ∈ (∅ : FiniteCube.Index 1) then Xprime else X) = X
    exact ite_eq_right (Finset.notMem_empty (0 : Fin 1))
  have hY : M.obj Finset.univ = Xprime := by
    change (if (0 : Fin 1) ∈ (Finset.univ : FiniteCube.Index 1) then Xprime else X) = Xprime
    exact ite_eq_left (Finset.mem_univ (0 : Fin 1))
  have hg : HEq (M.map f) x :=
    FiniteCube.familyMap_added (fun _ : Fin 1 => x) (Finset.empty_subset Finset.univ)
      (0 : Fin 1) (Finset.notMem_empty _) (Finset.mem_univ _)
  have hc : HEq (M.map f r) (x r) :=
    functorMapHEq (Pi.eval (fun _ : W => C) r) _ _ hX hY hg
  have hm : (markedInputCarrier x).map
      (show (∅, Discrete.mk r) ⟶ (Finset.univ, Discrete.mk r) from
        (f, 𝟙 (Discrete.mk r))) = M.map f r := by
    change M.map f r ≫ (Discrete.functor (M.obj Finset.univ)).map (𝟙 (Discrete.mk r)) = _
    rw [Functor.map_id]
    exact Category.comp_id (M.map f r)
  exact (heq_of_eq hm).trans hc

/-- Every original marked cube face is the original heterogeneous X/X′ face
under the actual original leaf-object comparison. -/
theorem profileMarkedLeafFamilyIso_face {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) {S T : FiniteCube.Index (inputCount P)} (f : S ⟶ T) :
    (FiniteFamily.map (markedInputCarrier x)).map ((profileMarkedCube P).map f) ≫
        (profileMarkedLeafFamilyIso x P T).hom =
      (profileMarkedLeafFamilyIso x P S).hom ≫ (rawProfileLeafCube x P).map f := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    change Fin (inputCount P) at i
    change HEq
      ((markedInputCarrier x).map (FiniteCube.familyMap (profileMarkedArrows P) (leOfHom f) i) ≫
        eqToHom (profileMarkedCarrier_vertex x P T i))
      (eqToHom (profileMarkedCarrier_vertex x P S i) ≫
        FiniteCube.familyMap (profileArrowFamily x P) (leOfHom f) i)
    let K := markedInputCarrier x
    let m := FiniteCube.familyMap (profileMarkedArrows P) (leOfHom f) i
    let l := FiniteCube.familyMap (profileArrowFamily x P) (leOfHom f) i
    have h : HEq (K.map m) l := by
      by_cases hS : i ∈ S
      · have hT : i ∈ T := leOfHom f hS
        have eS : FiniteCube.vertexFamily (profileDomainMarks P) (profileTopMarks P) S i =
            profileTopMarks P i := ite_eq_left hS
        have eT : FiniteCube.vertexFamily (profileDomainMarks P) (profileTopMarks P) T i =
            profileTopMarks P i := ite_eq_left hT
        have hm := functorMapHEq K m (𝟙 (profileTopMarks P i)) eS eT
          (FiniteCube.familyMap_selected (profileMarkedArrows P) (leOfHom f) i hS)
        have e := markedCarrier_top x (P.inputColor (inputEnumeration P i))
        have hid := (eqToHom_heq_id_dom _ _ e).symm.trans (eqToHom_heq_id_cod _ _ e)
        exact hm.trans ((heq_of_eq (K.map_id _)).trans
          (hid.trans (FiniteCube.familyMap_selected (profileArrowFamily x P) (leOfHom f) i hS).symm))
      · by_cases hT : i ∈ T
        · have eS : FiniteCube.vertexFamily (profileDomainMarks P) (profileTopMarks P) S i =
              profileDomainMarks P i := ite_eq_right hS
          have eT : FiniteCube.vertexFamily (profileDomainMarks P) (profileTopMarks P) T i =
              profileTopMarks P i := ite_eq_left hT
          have hm := functorMapHEq K m (profileMarkedArrows P i) eS eT
            (FiniteCube.familyMap_added (profileMarkedArrows P) (leOfHom f) i hS hT)
          exact hm.trans ((markedInputCarrier_arrow x (P.inputColor (inputEnumeration P i))).trans
            (FiniteCube.familyMap_added (profileArrowFamily x P) (leOfHom f) i hS hT).symm)
        · have eS : FiniteCube.vertexFamily (profileDomainMarks P) (profileTopMarks P) S i =
              profileDomainMarks P i := ite_eq_right hS
          have eT : FiniteCube.vertexFamily (profileDomainMarks P) (profileTopMarks P) T i =
              profileDomainMarks P i := ite_eq_right hT
          have hm := functorMapHEq K m (𝟙 (profileDomainMarks P i)) eS eT
            (FiniteCube.familyMap_unselected (profileMarkedArrows P) (leOfHom f) i hT)
          have e := markedCarrier_old x ∅ FiniteCube.puncturedOneEmpty.2
            (P.inputColor (inputEnumeration P i))
          have hid := (eqToHom_heq_id_dom _ _ e).symm.trans (eqToHom_heq_id_cod _ _ e)
          exact hm.trans ((heq_of_eq (K.map_id _)).trans
            (hid.trans (FiniteCube.familyMap_unselected (profileArrowFamily x P) (leOfHom f) i hT).symm))
    exact heq_of_eq (squareOfHEq (K.map m) l
      (profileMarkedCarrier_vertex x P S i) (profileMarkedCarrier_vertex x P T i) h)
end source_InitialAttachment_CubeTensor_Pure

section source_InitialAttachment_InputSetEquivalence
universe uc u v us


open CategoryTheory Limits MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {W : Type uc}

/-- The original finite input set has its classical decidable equality. -/
local instance setEquivalenceInputDecidableEq (P : ColoredProfile W) : DecidableEq P.inputs := Classical.decEq _

/-- Enumerate the original subset through the actual original input bijection. -/
def profileInputSetMap (P : ColoredProfile W) (S : FiniteCube.Index (inputCount P)) : ProfileInputSets P :=
  S.map (inputEnumeration P).toEmbedding

/-- Recover the original ordered subset through that same input bijection. -/
def profileInputSetInv (P : ColoredProfile W) (S : ProfileInputSets P) : FiniteCube.Index (inputCount P) :=
  S.map (inputEnumeration P).symm.toEmbedding

theorem profileInputSetMap_mono (P : ColoredProfile W) {S T : FiniteCube.Index (inputCount P)} (h : S ⊆ T) :
    profileInputSetMap P S ⊆ profileInputSetMap P T := Finset.map_subset_map.mpr h

theorem profileInputSetInv_mono (P : ColoredProfile W) {S T : ProfileInputSets P} (h : S ⊆ T) :
    profileInputSetInv P S ⊆ profileInputSetInv P T := Finset.map_subset_map.mpr h

/-- The original input enumeration preserves every actual subset inclusion. -/
def profileInputSetFunctor (P : ColoredProfile W) : FiniteCube.Index (inputCount P) ⥤ ProfileInputSets P :=
  (show Monotone (profileInputSetMap P) from fun _ _ h => profileInputSetMap_mono P h).functor

/-- The inverse original enumeration preserves every actual subset inclusion. -/
def profileInputSetInverseFunctor (P : ColoredProfile W) : ProfileInputSets P ⥤ FiniteCube.Index (inputCount P) :=
  (show Monotone (profileInputSetInv P) from fun _ _ h => profileInputSetInv_mono P h).functor

theorem profileInputSetMapInv (P : ColoredProfile W) (S : ProfileInputSets P) :
    profileInputSetMap P (profileInputSetInv P S) = S := by
  apply Finset.ext
  intro i
  simp only [profileInputSetMap, profileInputSetInv, Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]

theorem profileInputSetInvMap (P : ColoredProfile W) (S : FiniteCube.Index (inputCount P)) :
    profileInputSetInv P (profileInputSetMap P S) = S := by
  apply Finset.ext
  intro i
  simp only [profileInputSetMap, profileInputSetInv, Finset.mem_map_equiv, Equiv.symm_symm, Equiv.symm_apply_apply]

/-- The actual original finite input set cube is equivalent to its canonical
ordered FiniteCube presentation through the original input enumeration. -/
def profileInputSetEquivalence (P : ColoredProfile W) : FiniteCube.Index (inputCount P) ≌ ProfileInputSets P :=
  Equivalence.mk (profileInputSetFunctor P) (profileInputSetInverseFunctor P)
    (NatIso.ofComponents (fun S => eqToIso (profileInputSetInvMap P S).symm) (by intros; subsingleton))
    (NatIso.ofComponents (fun S => eqToIso (profileInputSetMapInv P S)) (by intros; subsingleton))

theorem profileInputSetMap_univ (P : ColoredProfile W) :
    profileInputSetMap P Finset.univ = Finset.univ := by
  apply Finset.ext
  intro i
  simp only [profileInputSetMap, Finset.mem_map_equiv, Finset.mem_univ]

theorem profileInputSetInv_univ (P : ColoredProfile W) :
    profileInputSetInv P Finset.univ = Finset.univ := by
  apply Finset.ext
  intro i
  simp only [profileInputSetInv, Finset.mem_map_equiv, Finset.mem_univ]

theorem profileInputSetMap_punctured (P : ColoredProfile W) (S : FiniteCube.Punctured (inputCount P)) :
    profileInputSetMap P S.1 ≠ Finset.univ := by
  intro h
  apply S.2
  exact (profileInputSetInvMap P S.1).symm.trans
    ((congrArg (profileInputSetInv P) h).trans (profileInputSetInv_univ P))

theorem profileInputSetInv_punctured (P : ColoredProfile W) (S : ProfilePuncturedInputSets P) :
    profileInputSetInv P S.1 ≠ Finset.univ := by
  intro h
  apply S.2
  exact (profileInputSetMapInv P S.1).symm.trans
    ((congrArg (profileInputSetMap P) h).trans (profileInputSetMap_univ P))

/-- The original input enumeration retains precisely the original proper faces. -/
def profilePuncturedSetFunctor (P : ColoredProfile W) :
    FiniteCube.Punctured (inputCount P) ⥤ ProfilePuncturedInputSets P where
  obj S := ⟨profileInputSetMap P S.1, profileInputSetMap_punctured P S⟩
  map h := homOfLE (profileInputSetMap_mono P (leOfHom h))

/-- The inverse original enumeration retains precisely the original proper faces. -/
def profilePuncturedSetInverseFunctor (P : ColoredProfile W) :
    ProfilePuncturedInputSets P ⥤ FiniteCube.Punctured (inputCount P) where
  obj S := ⟨profileInputSetInv P S.1, profileInputSetInv_punctured P S⟩
  map h := homOfLE (profileInputSetInv_mono P (leOfHom h))

/-- The same original input enumeration identifies precisely the two
original punctured cube categories, without adding or losing a face. -/
def profilePuncturedSetEquivalence (P : ColoredProfile W) :
    FiniteCube.Punctured (inputCount P) ≌ ProfilePuncturedInputSets P :=
  Equivalence.mk (profilePuncturedSetFunctor P) (profilePuncturedSetInverseFunctor P)
    (NatIso.ofComponents (fun S => eqToIso (Subtype.ext (profileInputSetInvMap P S.1).symm))
      (by intros; subsingleton))
    (NatIso.ofComponents (fun S => eqToIso (Subtype.ext (profileInputSetMapInv P S.1)))
      (by intros; subsingleton))
end source_InitialAttachment_InputSetEquivalence

section source_InitialAttachment_CubeIndexReindex
universe uc u v us


open CategoryTheory Limits MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {W : Type uc}

/-- The actual original profile enumeration is the complete input/color
bijection between the canonical marked cube and the original input-set cube. -/
def canonicalOriginalInputVertexIso (P : ColoredProfile W) (S : FiniteCube.Index (inputCount P)) :
    (profileMarkedCube P).obj S ≅ (originalInputCube P).obj (profileInputSetMap P S) :=
  FiniteFamily.isoOfComponents (inputEnumeration P) (fun i => eqToIso (Prod.ext
    (by
      change Fin (inputCount P) at i
      change (if i ∈ S then profileTopMarks P i else profileDomainMarks P i).1 =
        inputCoordinate P (profileInputSetMap P S) (inputEnumeration P i)
      simp only [inputCoordinate, profileInputSetMap, Finset.mem_map_equiv]
      have h := (inputEnumeration P).symm_apply_apply i
      have hs : (if i ∈ S then profileTopMarks P i else profileDomainMarks P i).1 =
          (if i ∈ S then (Finset.univ : FiniteCube.Index 1) else ∅) := by
        split <;> rfl
      exact hs.trans (congrArg (fun j : Fin (inputCount P) =>
        if j ∈ S then (Finset.univ : FiniteCube.Index 1) else ∅) h).symm)
    (by
      change (((profileMarkedCube P).obj S).obj i).2 = Discrete.mk (P.inputColor (inputEnumeration P i))
      exact congrArg Discrete.mk (profileMarkedCube_color P S i))))

theorem canonicalOriginalInputVertexIso_face (P : ColoredProfile W)
    {S T : FiniteCube.Index (inputCount P)} (f : S ⟶ T) :
    (profileMarkedCube P).map f ≫ (canonicalOriginalInputVertexIso P T).hom =
      (canonicalOriginalInputVertexIso P S).hom ≫
        (originalInputCube P).map ((profileInputSetFunctor P).map f) :=
  markedHom_ext rfl

section Geometry

variable {C : Type u} [Category.{v} C]

/-- Applying any genuine original coefficient/input diagram retains the
full canonical-to-original cube comparison, including every original face. -/
def canonicalOriginalInputCubeIso (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) :
    profileMarkedCube P ⋙ D ≅ profileInputSetFunctor P ⋙ geometryInputTensorCube D P :=
  NatIso.ofComponents (fun S => D.mapIso (canonicalOriginalInputVertexIso P S))
    (fun f => (D.map_comp _ _).symm.trans
      ((congrArg D.map (canonicalOriginalInputVertexIso_face P f)).trans (D.map_comp _ _)))

/-- The same source comparison restricts to precisely the original proper
faces, with no altered boundary diagram. -/
def canonicalOriginalPuncturedCubeIso (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) :
    FiniteCube.punctured (profileMarkedCube P ⋙ D) ≅
      profilePuncturedSetFunctor P ⋙ geometryPuncturedTensor D P :=
  NatIso.ofComponents (fun S => D.mapIso (canonicalOriginalInputVertexIso P S.1))
    (fun f => (D.map_comp _ _).symm.trans
      ((congrArg D.map (canonicalOriginalInputVertexIso_face P
        ((FiniteCube.puncturedInclusion (inputCount P)).map f))).trans (D.map_comp _ _)))


end Geometry
end source_InitialAttachment_CubeIndexReindex

section source_InitialAttachment_BoundaryIndexReindex
universe uc u v us


open CategoryTheory Limits MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {W : Type uc} {C : Type u} [Category.{v} C] [HasColimitsOfSize.{us, us} C]

local instance boundaryReindexSmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

/-- The exact original input enumeration identifies both actual punctured
boundary colimits, through the actual original diagram and category isos. -/
def canonicalOriginalBoundaryIso (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) :
    FiniteCube.boundary (profileMarkedCube P ⋙ D) ≅ geometryInputBoundary D P :=
  HasColimit.isoOfNatIso (canonicalOriginalPuncturedCubeIso D P) ≪≫
    Functor.Final.colimitIso (profilePuncturedSetEquivalence P).functor (geometryPuncturedTensor D P)

/-- The actual top comparison uses the same original input enumeration and
the original finite-set-to-top equality. -/
def canonicalOriginalTopIso (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) :
    (profileMarkedCube P ⋙ D).obj Finset.univ ≅ (geometryInputTensorCube D P).obj Finset.univ :=
  D.mapIso (canonicalOriginalInputVertexIso P Finset.univ) ≪≫
    (geometryInputTensorCube D P).mapIso (eqToIso (profileInputSetMap_univ P))

theorem canonicalOriginalBoundaryIso_face (D : MarkedInputs W ⥤ C) (P : ColoredProfile W)
    (S : FiniteCube.Punctured (inputCount P)) :
    FiniteCube.boundaryι (profileMarkedCube P ⋙ D) S ≫ (canonicalOriginalBoundaryIso D P).hom =
      D.map (canonicalOriginalInputVertexIso P S.1).hom ≫
        colimit.ι (geometryPuncturedTensor D P) ((profilePuncturedSetFunctor P).obj S) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (Functor.Final.colimitIso (profilePuncturedSetEquivalence P).functor
      (geometryPuncturedTensor D P)).hom)
        (HasColimit.ι_isoOfNatIso_hom (canonicalOriginalPuncturedCubeIso D P) S)).trans
          ((Category.assoc _ _ _).trans
            (congrArg (D.map (canonicalOriginalInputVertexIso P S.1).hom ≫ ·)
              (Functor.Final.ι_colimitIso_hom (profilePuncturedSetEquivalence P).functor
                (geometryPuncturedTensor D P) S))))

/-- The full original boundary-to-top arrow is retained by the actual
canonical-to-original input-set comparison on every original proper face. -/
theorem canonicalOriginalBoundaryTop_square (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) :
    (canonicalOriginalBoundaryIso D P).hom ≫ geometryBoundaryToTop D P =
      FiniteCube.boundaryToTop (profileMarkedCube P ⋙ D) ≫ (canonicalOriginalTopIso D P).hom := by
  let F := geometryInputTensorCube D P
  let N := profileMarkedCube P ⋙ D
  apply FiniteCube.boundary_hom_ext N
  intro S
  let q : S.1 ⟶ (Finset.univ : FiniteCube.Index (inputCount P)) := homOfLE (Finset.subset_univ S.1)
  let r := (profileInputSetFunctor P).map q
  let e : profileInputSetMap P Finset.univ ⟶ (Finset.univ : ProfileInputSets P) :=
    eqToHom (profileInputSetMap_univ P)
  let t : profileInputSetMap P S.1 ⟶ (Finset.univ : ProfileInputSets P) :=
    homOfLE (Finset.subset_univ _)
  have hn : N.map q ≫ D.map (canonicalOriginalInputVertexIso P Finset.univ).hom =
      D.map (canonicalOriginalInputVertexIso P S.1).hom ≫ F.map r :=
    (D.map_comp _ _).symm.trans
      ((congrArg D.map (canonicalOriginalInputVertexIso_face P q)).trans (D.map_comp _ _))
  have he : F.map r ≫ F.map e = F.map t :=
    (F.map_comp r e).symm.trans (congrArg F.map (Subsingleton.elim (r ≫ e) t))
  have hright : FiniteCube.boundaryι N S ≫
      (FiniteCube.boundaryToTop N ≫ (canonicalOriginalTopIso D P).hom) =
        D.map (canonicalOriginalInputVertexIso P S.1).hom ≫ F.map t :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (canonicalOriginalTopIso D P).hom) (FiniteCube.boundaryι_boundaryToTop N S)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ F.map e) hn).trans
            ((Category.assoc _ _ _).trans
              (congrArg (D.map (canonicalOriginalInputVertexIso P S.1).hom ≫ ·) he)))))
  have hleft : FiniteCube.boundaryι N S ≫
      ((canonicalOriginalBoundaryIso D P).hom ≫ geometryBoundaryToTop D P) =
        D.map (canonicalOriginalInputVertexIso P S.1).hom ≫ F.map t :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ geometryBoundaryToTop D P) (canonicalOriginalBoundaryIso_face D P S)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (D.map (canonicalOriginalInputVertexIso P S.1).hom ≫ ·)
            (geometryBoundaryToTop_face D P ((profilePuncturedSetFunctor P).obj S)))))
  exact hleft.trans hright.symm

/-- The actual original input-set full attaching arrow is the canonical
original FiniteCube attaching arrow, with both source and target maps retained. -/
def canonicalOriginalInputArrowIso (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) :
    Arrow.mk (FiniteCube.boundaryToTop (profileMarkedCube P ⋙ D)) ≅ Arrow.mk (geometryBoundaryToTop D P) :=
  Arrow.isoMk (canonicalOriginalBoundaryIso D P) (canonicalOriginalTopIso D P)
    (canonicalOriginalBoundaryTop_square D P)
end source_InitialAttachment_BoundaryIndexReindex


section source_ProfileCellDecomposition_ArrowColimits
universe uj vj u v

variable {J : Type uj} [Category.{vj} J] {C : Type u} [Category.{v} C]
variable {A B : J ⥤ C} [HasColimit A] [HasColimit B]

-- These existing public names retain the boundary used by saved consumers.
-- Every value is the single neutral implementation.
/-- The canonical whole-Arrow cocone of a natural transformation, retaining
both actual endpoint colimits and their induced Arrow. -/
abbrev naturalArrowCocone (a : A ⟶ B) : Cocone (naturalArrowFunctor a) :=
  CategoryTheory.naturalArrowCocone a

/-- Project the original whole-Arrow cocone to its source endpoint cocone. -/
abbrev naturalArrowTargetLeft (a : A ⟶ B) (c : Cocone (naturalArrowFunctor a)) : Cocone A :=
  CategoryTheory.naturalArrowTargetLeft a c

/-- Project the original whole-Arrow cocone to its target endpoint cocone. -/
abbrev naturalArrowTargetRight (a : A ⟶ B) (c : Cocone (naturalArrowFunctor a)) : Cocone B :=
  CategoryTheory.naturalArrowTargetRight a c

theorem naturalArrowDesc_square (a : A ⟶ B) (c : Cocone (naturalArrowFunctor a)) :
    colimit.desc A (naturalArrowTargetLeft a c) ≫ c.pt.hom =
      colimMap a ≫ colimit.desc B (naturalArrowTargetRight a c) :=
  CategoryTheory.naturalArrowDesc_square a c

/-- The unique whole-Arrow map from the canonical colimit cocone to the
supplied cocone, with both original endpoint descenders. -/
abbrev naturalArrowDesc (a : A ⟶ B) (c : Cocone (naturalArrowFunctor a)) :
    (naturalArrowCocone a).pt ⟶ c.pt := CategoryTheory.naturalArrowDesc a c

theorem naturalArrowDesc_fac (a : A ⟶ B) (c : Cocone (naturalArrowFunctor a)) (j : J) :
    (naturalArrowCocone a).ι.app j ≫ naturalArrowDesc a c = c.ι.app j :=
  CategoryTheory.naturalArrowDesc_fac a c j

theorem naturalArrowDesc_unique (a : A ⟶ B) (c : Cocone (naturalArrowFunctor a))
    (m : (naturalArrowCocone a).pt ⟶ c.pt)
    (w : ∀ j, (naturalArrowCocone a).ι.app j ≫ m = c.ι.app j) : m = naturalArrowDesc a c :=
  CategoryTheory.naturalArrowDesc_unique a c m w

/-- Both original endpoint colimit properties give the universal property
of the canonical whole-Arrow cocone. -/
abbrev naturalArrowIsColimit (a : A ⟶ B) : IsColimit (naturalArrowCocone a) :=
  CategoryTheory.naturalArrowIsColimit a

end source_ProfileCellDecomposition_ArrowColimits

end CategoryTheory.OperadicOrbitCells.ProfileGeometry

namespace CategoryTheory.OperadicOrbitCells

section source_OrbitCells_GeneralOrbit
universe ug u v


open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory
open ProfileGeometry

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {G : Type ug} [Group G] [HasColimitsOfShape (SingleObj G) C]

/-- The actual map between the original two coefficient-action orbit colimits. -/
def coefficientOrbitArrow (Y : Action C G) {B T : Action C G} (p : B ⟶ T) : Arrow C :=
  Arrow.mk (colimMap (coefficientTransformation Y p))

/-- The coefficient tensor arrow before taking its action quotient. -/
def coefficientUnderlyingArrow (Y : Action C G) {B T : Action C G} (p : B ⟶ T) : Arrow C :=
  Arrow.mk (Y.V ◁ p.hom)

/-- The actual two orbit projections form the whole original Arrow cocone. -/
def coefficientOrbitCocone (Y : Action C G) {B T : Action C G} (p : B ⟶ T) :
    Cocone (CategoryTheory.naturalArrowFunctor (coefficientTransformation Y p)) :=
  CategoryTheory.naturalArrowCocone (coefficientTransformation Y p)

/-- The whole Arrow colimit retains both descenders and their uniqueness. -/
def coefficientOrbitIsColimit (Y : Action C G) {B T : Action C G} (p : B ⟶ T) :
    IsColimit (coefficientOrbitCocone Y p) :=
  CategoryTheory.naturalArrowIsColimit (coefficientTransformation Y p)

/-- The original source projection of the actual whole Arrow orbit cocone. -/
theorem coefficientOrbitCocone_left (Y : Action C G) {B T : Action C G} (p : B ⟶ T) :
    ((coefficientOrbitCocone Y p).ι.app (SingleObj.star G)).left =
      colimit.ι (coefficientSourceFunctor Y B) (SingleObj.star G) := rfl

/-- The original target projection of the actual whole Arrow orbit cocone. -/
theorem coefficientOrbitCocone_right (Y : Action C G) {B T : Action C G} (p : B ⟶ T) :
    ((coefficientOrbitCocone Y p).ι.app (SingleObj.star G)).right =
      colimit.ι (coefficientSourceFunctor Y T) (SingleObj.star G) := rfl

/-- The actual source orbit projection and target orbit projection retain the original arrow. -/
@[reassoc]
theorem coefficientOrbit_square (Y : Action C G) {B T : Action C G} (p : B ⟶ T) :
    colimit.ι (coefficientSourceFunctor Y B) (SingleObj.star G) ≫
        (coefficientOrbitArrow Y p).hom =
      (Y.V ◁ p.hom) ≫ colimit.ι (coefficientSourceFunctor Y T) (SingleObj.star G) :=
  ι_colimMap (coefficientTransformation Y p) (SingleObj.star G)

/-- The true single-object action category is terminal when its group is trivial. -/
def trivialGroupTerminal [Subsingleton G] : IsTerminal (SingleObj.star G) :=
  IsTerminal.ofUniqueHom (fun _ => (1 : G)) (fun _ _ => Subsingleton.elim _ _)

/-- With a trivial acting group, the actual two quotient projections are isomorphisms. -/
def coefficientOrbitTrivialGroupIso [Subsingleton G]
    (Y : Action C G) {B T : Action C G} (p : B ⟶ T) :
    coefficientUnderlyingArrow Y p ≅ coefficientOrbitArrow Y p := by
  have hB : IsIso (colimit.ι (coefficientSourceFunctor Y B) (SingleObj.star G)) :=
    (colimit.isColimit (coefficientSourceFunctor Y B)).isIso_ι_app_of_isTerminal
      (SingleObj.star G) (trivialGroupTerminal (G := G))
  have hT : IsIso (colimit.ι (coefficientSourceFunctor Y T) (SingleObj.star G)) :=
    (colimit.isColimit (coefficientSourceFunctor Y T)).isIso_ι_app_of_isTerminal
      (SingleObj.star G) (trivialGroupTerminal (G := G))
  exact Arrow.isoMk
    (@asIso _ _ _ _ (colimit.ι (coefficientSourceFunctor Y B) (SingleObj.star G)) hB)
    (@asIso _ _ _ _ (colimit.ι (coefficientSourceFunctor Y T) (SingleObj.star G)) hT)
    (coefficientOrbit_square Y p)

/-- The exact tensor unit gives the actual original action arrow after forgetting the action. -/
def coefficientUnderlyingUnitIso {B T : Action C G} (p : B ⟶ T) :
    coefficientUnderlyingArrow (𝟙_ (Action C G)) p ≅ Arrow.mk p.hom :=
  Arrow.isoMk (λ_ B.V) (λ_ T.V) (leftUnitor_naturality p.hom).symm

/-- The complete unary/trivial-group unit normalization uses both original quotient projections. -/
def coefficientOrbitUnitIso [Subsingleton G] {B T : Action C G} (p : B ⟶ T) :
    coefficientOrbitArrow (𝟙_ (Action C G)) p ≅ Arrow.mk p.hom :=
  (coefficientOrbitTrivialGroupIso (𝟙_ (Action C G)) p).symm ≪≫
    coefficientUnderlyingUnitIso p
end source_OrbitCells_GeneralOrbit
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells

section source_OrbitCells_ArrowAction
universe ug u v


open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory
open ProfileGeometry

variable {C : Type u} [Category.{v} C] {G : Type ug} [Group G]

section Coefficients

variable [MonoidalCategory C] [HasColimitsOfShape (SingleObj G) C]

/-- Tensor by an arbitrary equivariant coefficient, then take the original action orbit. -/
def coefficientOrbitFunctor (Y : Action C G) : Action (Arrow C) G ⥤ Arrow C :=
  CategoryTheory.naturalArrowFunctor
    (Functor.whiskerRight Action.underlyingActionTransformation
      (tensorLeft Y ⋙ (Action.coinvariantsFunctor (C := C) G)))

/-- The functor's whole Arrow object is the literal coefficient orbit arrow. -/
theorem coefficientOrbitFunctor_obj (Y : Action C G) (A : Action (Arrow C) G) :
    (coefficientOrbitFunctor Y).obj A = coefficientOrbitArrow Y (Action.actionUnderlyingHom A) := rfl

/-- Every original isomorphism of whole-arrow actions gives the actual orbit Arrow iso. -/
def coefficientOrbitActionIso (Y : Action C G) {A B : Action (Arrow C) G}
    (e : A ≅ B) :
    coefficientOrbitArrow Y (Action.actionUnderlyingHom A) ≅
      coefficientOrbitArrow Y (Action.actionUnderlyingHom B) :=
  (coefficientOrbitFunctor Y).mapIso e

/-- Both original coefficient/action quotient maps are retained under whole-arrow transport. -/
def coefficientOrbitTransportIso (Y : Action C G) (A : Action (Arrow C) G)
    {B : Arrow C} (e : A.V ≅ B) :
    coefficientOrbitArrow Y (Action.actionUnderlyingHom A) ≅
      coefficientOrbitArrow Y (Action.actionUnderlyingHom (Action.transportArrowAction A e)) :=
  coefficientOrbitActionIso Y (Action.transportArrowActionIso A e)

end Coefficients
end source_OrbitCells_ArrowAction
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells

section source_OrbitCells_PlainProfile
universe uc u v us


open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory
open Operad ProfileGeometry
open ProfileGeometry

attribute [local instance] FintypeCat.fintype

variable {W : Type uc} {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [SymmetricCategory C]

/-- The actual input diagrams use the canonical original symmetric finite tensor. -/
local instance inputFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C

/-- Tensor the actual original finite marked input family, with no coefficient. -/
def inputTensorDiagram {X Xprime : W → C} (x : X ⟶ Xprime) : MarkedInputs W ⥤ C :=
  FiniteFamily.map (markedInputCarrier x) ⋙ FiniteTensor.tensor

variable [HasColimitsOfSize.{us, us} C]

local instance inputSmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

local instance inputAutColimits (P : ColoredProfile W) :
    HasColimitsOfShape (SingleObj (Aut P)) C :=
  HasColimitsOfShape.of_essentiallySmall C _

/-- The boundary action is the actual action on the full original proper-face colimit. -/
def inputBoundaryAction {X Xprime : W → C} (x : X ⟶ Xprime) (P : ColoredProfile W) :
    Action C (Aut P) :=
  (Action.functorCategoryEquivalence C (Aut P)).inverse.obj
    (geometryBoundaryActionFunctor (inputTensorDiagram x) P)

/-- The top action uses the same original input permutation at the full top. -/
def inputTopAction {X Xprime : W → C} (x : X ⟶ Xprime) (P : ColoredProfile W) :
    Action C (Aut P) :=
  (Action.functorCategoryEquivalence C (Aut P)).inverse.obj
    (geometryInputTopActionFunctor (inputTensorDiagram x) P)

/-- The full original finite pushout-product boundary arrow is an actual action morphism. -/
def inputActionArrow {X Xprime : W → C} (x : X ⟶ Xprime) (P : ColoredProfile W) :
    inputBoundaryAction x P ⟶ inputTopAction x P :=
  (Action.functorCategoryEquivalence C (Aut P)).inverse.map
    (geometryBoundaryTopTransformation (inputTensorDiagram x) P)

/-- The unchanged full boundary-to-top arrow remains the underlying map. -/
theorem inputActionArrow_hom {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) :
    (inputActionArrow x P).hom = geometryBoundaryToTop (inputTensorDiagram x) P := rfl

/-- Every original proper face retains its original full tensor map to the top. -/
@[reassoc]
theorem inputActionArrow_face {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (S : ProfilePuncturedInputSets P) :
    colimit.ι (geometryPuncturedTensor (inputTensorDiagram x) P) S ≫
        (inputActionArrow x P).hom =
      (geometryInputTensorCube (inputTensorDiagram x) P).map
        (homOfLE (Finset.subset_univ S.1)) :=
  geometryBoundaryToTop_face (inputTensorDiagram x) P S

/-- The source action is the actual permutation action on its original proper-face colimit. -/
theorem inputBoundaryAction_map {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (g : Aut P) :
    ((inputBoundaryAction x P).ρ g).asHom =
      geometryAutMap (inputTensorDiagram x) P g := rfl

omit [HasColimitsOfSize.{us, us} C] in
/-- The target action is the actual original full-input permutation. -/
theorem inputTopAction_map {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (g : Aut P) :
    ((inputTopAction x P).ρ g).asHom =
      (geometryInputTopRepresentation (inputTensorDiagram x) P g).asHom := rfl

/-- Equivariance follows from the original input diagram, without a supplied outcome. -/
theorem inputActionArrow_equivariance {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (g : Aut P) :
    ((inputBoundaryAction x P).ρ g).asHom ≫ (inputActionArrow x P).hom =
      (inputActionArrow x P).hom ≫ ((inputTopAction x P).ρ g).asHom :=
  geometryBoundaryToTop_equivariance (inputTensorDiagram x) P g

/-- Tensor every arbitrary equivariant coefficient with the actual original input arrow. -/
def profileOrbitArrow {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (Y : Action C (Aut P)) : Arrow C :=
  coefficientOrbitArrow Y (inputActionArrow x P)

/-- Both original coefficient/action orbit projections form its actual whole Arrow cocone. -/
def profileOrbitCocone {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (Y : Action C (Aut P)) :
    Cocone (CategoryTheory.naturalArrowFunctor (coefficientTransformation Y (inputActionArrow x P))) :=
  coefficientOrbitCocone Y (inputActionArrow x P)

/-- The full original Arrow colimit retains both coefficient and input action maps. -/
def profileOrbitIsColimit {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (Y : Action C (Aut P)) :
    IsColimit (profileOrbitCocone x P Y) :=
  coefficientOrbitIsColimit Y (inputActionArrow x P)

section OrderedComparison

variable [MonoidalClosed C]

/-- The original marked leaf objects, followed by the checked original enumeration. -/
def inputOrderedCubeIso {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) :
    profileMarkedCube P ⋙ inputTensorDiagram x ≅
      FiniteCube.tensorCube (profileArrowFamily x P) :=
  NatIso.ofComponents
    (fun S => (FiniteTensor.tensor (V := C)).mapIso (profileMarkedLeafFamilyIso x P S) ≪≫
      fixedToOrderedIso (FiniteCube.vertexFamily
        (fun i => X (P.inputColor (inputEnumeration P i)))
        (fun i => Xprime (P.inputColor (inputEnumeration P i))) S))
    (by
      intro S T f
      let A := FiniteTensor.tensor (V := C)
      have h₀ := (A.map_comp _ _).symm.trans
        ((congrArg A.map (profileMarkedLeafFamilyIso_face x P f)).trans (A.map_comp _ _))
      have h₁ := fixedToOrderedIso_naturality
        (FiniteCube.familyMap (profileArrowFamily x P) (leOfHom f))
      let eS := fixedToOrderedIso (FiniteCube.vertexFamily
        (fun i => X (P.inputColor (inputEnumeration P i)))
        (fun i => Xprime (P.inputColor (inputEnumeration P i))) S)
      let eT := fixedToOrderedIso (FiniteCube.vertexFamily
        (fun i => X (P.inputColor (inputEnumeration P i)))
        (fun i => Xprime (P.inputColor (inputEnumeration P i))) T)
      let l := (rawProfileLeafCube x P).map f
      let m := (FiniteCube.tensorCube (profileArrowFamily x P)).map f
      have h₁' : A.map l ≫ eT.hom = eS.hom ≫ m := h₁
      change A.map ((FiniteFamily.map (markedInputCarrier x)).map
          ((profileMarkedCube P).map f)) ≫
          (A.map (profileMarkedLeafFamilyIso x P T).hom ≫ eT.hom) =
        (A.map (profileMarkedLeafFamilyIso x P S).hom ≫ eS.hom) ≫ m
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ eT.hom) h₀).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (A.map (profileMarkedLeafFamilyIso x P S).hom ≫ ·) h₁').trans
              (Category.assoc _ _ _).symm))))

/-- The full original input-set attaching arrow is the actual iterated heterogeneous PP. -/
def inputPushoutProductIso {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) :
    Arrow.mk (inputActionArrow x P).hom ≅
      FiniteCube.iteratedPushoutProduct (profileArrowFamily x P) :=
  (canonicalOriginalInputArrowIso (inputTensorDiagram x) P).symm ≪≫
    FiniteCube.boundaryArrowIso (inputOrderedCubeIso x P) ≪≫
      FiniteCube.tensorBoundaryArrowIso (profileArrowFamily x P)

end OrderedComparison
end source_OrbitCells_PlainProfile
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells

section source_OrbitCells_IteratedProfile
universe uc u v us


open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory
open Operad ProfileGeometry
open ProfileGeometry

variable {W : Type uc} {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{us, us} C]

local instance iteratedSmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

local instance iteratedAutColimits (P : ColoredProfile W) :
    HasColimitsOfShape (SingleObj (Aut P)) C :=
  HasColimitsOfShape.of_essentiallySmall C _

/-- The constructed original input-set boundary and top form one whole-arrow action. -/
def rawProfileArrowAction {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) : Action (Arrow C) (Aut P) :=
  (Action.functorCategoryEquivalence (Arrow C) (Aut P)).inverse.obj
    (CategoryTheory.naturalArrowFunctor (geometryBoundaryTopTransformation (inputTensorDiagram x) P))

/-- The original full input-set Arrow iso transports the action to the actual iterated PP. -/
def profilePushoutProductAction {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) : Action (Arrow C) (Aut P) :=
  Action.transportArrowAction (rawProfileArrowAction x P) (inputPushoutProductIso x P)

/-- The complete underlying object is the original iterated heterogeneous pushout product. -/
theorem profilePushoutProductAction_V {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) :
    (profilePushoutProductAction x P).V =
      FiniteCube.iteratedPushoutProduct (profileArrowFamily x P) := rfl

/-- Every actual group map is the original permutation map through the full original Arrow iso. -/
theorem profilePushoutProductAction_map {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (g : Aut P) :
    ((profilePushoutProductAction x P).ρ g).asHom =
      (inputPushoutProductIso x P).inv ≫
        ((rawProfileArrowAction x P).ρ g).asHom ≫ (inputPushoutProductIso x P).hom :=
  Action.transportArrowAction_map (rawProfileArrowAction x P) (inputPushoutProductIso x P) g

/-- The actual full PP action has its actual source and target action objects. -/
def profilePushoutProductHom {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) :
    Action.leftActionFunctor.obj (profilePushoutProductAction x P) ⟶
      Action.rightActionFunctor.obj (profilePushoutProductAction x P) :=
  Action.actionUnderlyingHom (profilePushoutProductAction x P)

/-- The original whole attaching map, including its original source object, is retained. -/
theorem profilePushoutProductHom_hom {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) :
    (profilePushoutProductHom x P).hom =
      (FiniteCube.iteratedPushoutProduct (profileArrowFamily x P)).hom := rfl

/-- Every arbitrary equivariant coefficient weights the actual iterated PP before taking orbits. -/
def profileIteratedOrbitArrow {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (Y : Action C (Aut P)) : Arrow C :=
  coefficientOrbitArrow Y (profilePushoutProductHom x P)

/-- The actual source and target orbit projections form its whole original Arrow cocone. -/
def profileIteratedOrbitCocone {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (Y : Action C (Aut P)) :
    Cocone (CategoryTheory.naturalArrowFunctor (coefficientTransformation Y (profilePushoutProductHom x P))) :=
  coefficientOrbitCocone Y (profilePushoutProductHom x P)

/-- The full original iterated-PP Arrow colimit is built from the two actual orbit cocones. -/
def profileIteratedOrbitIsColimit {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (Y : Action C (Aut P)) :
    IsColimit (profileIteratedOrbitCocone x P Y) :=
  coefficientOrbitIsColimit Y (profilePushoutProductHom x P)

/-- The original input-set orbit and actual coefficient PP orbit are the same whole Arrow,
through the original source and target PP comparisons. -/
def profileOrbitPushoutProductIso {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (Y : Action C (Aut P)) :
    profileOrbitArrow x P Y ≅ profileIteratedOrbitArrow x P Y :=
  coefficientOrbitTransportIso Y (rawProfileArrowAction x P) (inputPushoutProductIso x P)
end source_OrbitCells_IteratedProfile
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells

section source_OrbitCells_MatrixFamily
universe u v us


open CategoryTheory Limits MonoidalCategory MorphismProperty
open scoped MonoidalCategory
open Operad ProfileGeometry
open ProfileGeometry

attribute [local instance] FintypeCat.fintype

/-- The actual product of the symmetric groups of the original positive multiplicities. -/
abbrev MultiplicityGroup {k : ℕ} (n : Fin k → ℕ) :=
  ∀ r : Fin k, Equiv.Perm (Fin (n r))

/-- The actual expanded finite profile, with one original color for each family member. -/
def multiplicityProfile {k : ℕ} (hk : 0 < k) (n : Fin k → ℕ) : ColoredProfile (Fin k) where
  inputs := FintypeCat.of (Σ r : Fin k, Fin (n r))
  inputColor := Sigma.fst
  outputColor := ⟨0, hk⟩

/-- The actual color fiber is exactly its original finite multiplicity tuple entry. -/
def multiplicityFiberEquiv {k : ℕ} (hk : 0 < k) (n : Fin k → ℕ) (r : Fin k) :
    ColorFiber (multiplicityProfile hk n) r ≃ Fin (n r) where
  toFun p := by
    rcases p with ⟨⟨s, i⟩, h⟩
    cases h
    exact i
  invFun i := ⟨⟨r, i⟩, rfl⟩
  left_inv p := by
    rcases p with ⟨⟨s, i⟩, h⟩
    cases h
    rfl
  right_inv _ := rfl

/-- The original fiber equivalence transports the actual fiber permutation group. -/
def multiplicityFiberPermutationEquiv {k : ℕ} (hk : 0 < k)
    (n : Fin k → ℕ) (r : Fin k) :
    Equiv.Perm (ColorFiber (multiplicityProfile hk n) r) ≃* Equiv.Perm (Fin (n r)) :=
  { (multiplicityFiberEquiv hk n r).permCongr with
    map_mul' := fun f g => ((multiplicityFiberEquiv hk n r).permCongr_trans g f).symm }

/-- The whole actual profile automorphism group is the displayed original product of Sigmas. -/
def multiplicityAutEquiv {k : ℕ} (hk : 0 < k) (n : Fin k → ℕ) :
    Aut (multiplicityProfile hk n) ≃* MultiplicityGroup n :=
  (profileAutFiberMulEquiv (multiplicityProfile hk n)).trans
    { toFun f := fun r => multiplicityFiberPermutationEquiv hk n r (f r)
      invFun f := fun r => (multiplicityFiberPermutationEquiv hk n r).symm (f r)
      left_inv f := funext (fun r =>
        (multiplicityFiberPermutationEquiv hk n r).symm_apply_apply (f r))
      right_inv f := funext (fun r =>
        (multiplicityFiberPermutationEquiv hk n r).apply_symm_apply (f r))
      map_mul' f g := funext (fun r =>
        (multiplicityFiberPermutationEquiv hk n r).map_mul (f r) (g r)) }

/-- Positive multiplicities force positive total new-variable degree. -/
theorem multiplicityProfile_inputCount_pos {k : ℕ} (hk : 0 < k)
    (n : Fin k → ℕ) (hn : ∀ r, 0 < n r) :
    0 < inputCount (multiplicityProfile hk n) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨0, hk⟩, ⟨0, hn ⟨0, hk⟩⟩⟩⟩

variable {C : Type u} [Category.{v} C]

/-- A genuine nonempty finite family, its original positive multiplicities,
and every arbitrary coefficient acted on by their original product of symmetric groups. -/
structure PositiveOrbitFamily (C : Type u) [Category.{v} C] where
  /-- The number of original finite family members. -/
  colors : ℕ
  colors_pos : 0 < colors
  /-- The original positive multiplicity attached to each family member. -/
  multiplicity : Fin colors → ℕ
  multiplicity_pos : ∀ r, 0 < multiplicity r
  /-- The original whole arrow of every finite family member. -/
  arrows : Fin colors → Arrow C
  /-- Every arbitrary object acted on by the original product of symmetric groups. -/
  coefficient : Action C (MultiplicityGroup multiplicity)

section Geometry

variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{us, us} C]

local instance matrixSmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

local instance matrixGroupColimits {k : ℕ} (n : Fin k → ℕ) :
    HasColimitsOfShape (SingleObj (MultiplicityGroup n)) C :=
  HasColimitsOfShape.of_essentiallySmall C _

/-- The original family is the unchanged color-indexed ordinary arrow. -/
def matrixArrowFamily {k : ℕ} (f : Fin k → Arrow C) :
    (fun r => (f r).left) ⟶ (fun r => (f r).right) :=
  fun r => (f r).hom

/-- The actual product-Sigma action on the actual expanded heterogeneous PP. -/
def matrixPushoutProductAction {k : ℕ} (hk : 0 < k)
    (n : Fin k → ℕ) (f : Fin k → Arrow C) : Action (Arrow C) (MultiplicityGroup n) :=
  (Action.res (Arrow C) (multiplicityAutEquiv hk n).symm.toMonoidHom).obj
    (profilePushoutProductAction (matrixArrowFamily f) (multiplicityProfile hk n))

/-- The actual displayed product group acts by its actual original full profile permutation. -/
theorem matrixPushoutProductAction_map {k : ℕ} (hk : 0 < k)
    (n : Fin k → ℕ) (f : Fin k → Arrow C) (g : MultiplicityGroup n) :
    ((matrixPushoutProductAction hk n f).ρ g).asHom =
      ((profilePushoutProductAction (matrixArrowFamily f) (multiplicityProfile hk n)).ρ
        ((multiplicityAutEquiv hk n).symm g)).asHom := rfl

/-- Every arbitrary original product-Sigma coefficient weights the actual expanded PP. -/
def matrixOrbitArrow {k : ℕ} (hk : 0 < k) (n : Fin k → ℕ)
    (f : Fin k → Arrow C) (Y : Action C (MultiplicityGroup n)) : Arrow C :=
  coefficientOrbitArrow Y (Action.actionUnderlyingHom (matrixPushoutProductAction hk n f))

/-- Its source and target product-Sigma quotient projections form the whole Arrow cocone. -/
def matrixOrbitCocone {k : ℕ} (hk : 0 < k) (n : Fin k → ℕ)
    (f : Fin k → Arrow C) (Y : Action C (MultiplicityGroup n)) :
    Cocone (CategoryTheory.naturalArrowFunctor (coefficientTransformation Y
      (Action.actionUnderlyingHom (matrixPushoutProductAction hk n f)))) :=
  coefficientOrbitCocone Y (Action.actionUnderlyingHom (matrixPushoutProductAction hk n f))

/-- The full original Arrow colimit is built from both actual product-Sigma quotient cocones. -/
def matrixOrbitIsColimit {k : ℕ} (hk : 0 < k) (n : Fin k → ℕ)
    (f : Fin k → Arrow C) (Y : Action C (MultiplicityGroup n)) :
    IsColimit (matrixOrbitCocone hk n f Y) :=
  coefficientOrbitIsColimit Y (Action.actionUnderlyingHom (matrixPushoutProductAction hk n f))

/-- The positive-family source keeps every original arrow, multiplicity, and coefficient action. -/
def familyOrbitArrow (s : PositiveOrbitFamily C) : Arrow C :=
  matrixOrbitArrow s.colors_pos s.multiplicity s.arrows s.coefficient

/-- The conventional global class of positive finite coefficient-orbit PP generators. -/
def orbitGenerators (P : MorphismProperty C) : MorphismProperty C :=
  .ofHoms (fun q : {s : PositiveOrbitFamily C // ∀ r, P (s.arrows r).hom} =>
    (familyOrbitArrow q.1).hom)

/-- Every original positive finite family gives a literal generator in the same global class. -/
theorem familyOrbitArrow_mem (P : MorphismProperty C) (s : PositiveOrbitFamily C)
    (hs : ∀ r, P (s.arrows r).hom) : orbitGenerators P (familyOrbitArrow s).hom := by
  unfold orbitGenerators
  exact MorphismProperty.ofHoms.mk
    (⟨s, hs⟩ : {s : PositiveOrbitFamily C // ∀ r, P (s.arrows r).hom})

/-- Source membership is tested on every literal positive family and its actual coefficient orbit. -/
theorem orbitGenerators_le_iff (P Q : MorphismProperty C) :
    orbitGenerators P ≤ Q ↔ ∀ s : PositiveOrbitFamily C,
      (∀ r, P (s.arrows r).hom) → Q (familyOrbitArrow s).hom := by
  unfold orbitGenerators
  rw [MorphismProperty.ofHoms_le_iff]
  constructor
  · intro h s hs
    exact h ⟨s, hs⟩
  · intro h s
    exact h s.1 s.2

/-- Enlarging the original arrow class preserves every original positive family and coefficient. -/
theorem orbitGenerators_monotone : Monotone (orbitGenerators (C := C)) := by
  intro P Q h
  apply (orbitGenerators_le_iff P (orbitGenerators Q)).2
  intro s hs
  exact familyOrbitArrow_mem Q s (fun r => h _ (hs r))

/-- The arity-one source is a global positive family, independent of any operad palette. -/
def unaryOrbitFamily {A B : C} (f : A ⟶ B) : PositiveOrbitFamily C where
  colors := 1
  colors_pos := by decide
  multiplicity _ := 1
  multiplicity_pos _ := by decide
  arrows _ := Arrow.mk f
  coefficient := 𝟙_ (Action C (MultiplicityGroup (fun _ : Fin 1 => 1)))

/-- The underlying arity-one PP is literally the original whole Arrow. -/
theorem unaryPushoutProductAction_V {A B : C} (f : A ⟶ B) :
    (matrixPushoutProductAction (by decide : 0 < 1) (fun _ : Fin 1 => 1)
      (fun _ => Arrow.mk f)).V = Arrow.mk f := by
  let P := multiplicityProfile (by decide : 0 < 1) (fun _ : Fin 1 => 1)
  have h : inputCount P = 1 := by
    let _ : Unique P.inputs :=
      { default := ⟨0, 0⟩
        uniq := by
          rintro ⟨r, i⟩
          cases Subsingleton.elim r (0 : Fin 1)
          cases Subsingleton.elim i (0 : Fin 1)
          rfl }
    exact Fintype.card_unique
  change FiniteCube.iteratedPushoutProduct
    (fun _ : Fin (inputCount P) => f) = Arrow.mk f
  rw [h]
  rfl

/-- Both actual arity-one unit-coefficient orbit projections normalize to the original Arrow. -/
def unaryOrbitArrowIso {A B : C} (f : A ⟶ B) :
    familyOrbitArrow (unaryOrbitFamily f) ≅ Arrow.mk f := by
  let n := fun _ : Fin 1 => 1
  let a := matrixPushoutProductAction (by decide : 0 < 1) n (fun _ => Arrow.mk f)
  let _ : Subsingleton (MultiplicityGroup n) := inferInstance
  exact coefficientOrbitUnitIso (Action.actionUnderlyingHom a) ≪≫
    eqToIso (unaryPushoutProductAction_V f)

/-- Ordinary arrows enter the same global source class through the actual unary/unit Arrow iso. -/
theorem le_orbitGenerators_isoClosure (P : MorphismProperty C) :
    P ≤ (orbitGenerators P).isoClosure := by
  intro A B f hf
  exact ⟨_, _, (familyOrbitArrow (unaryOrbitFamily f)).hom,
    familyOrbitArrow_mem P (unaryOrbitFamily f) (fun _ => hf),
    ⟨unaryOrbitArrowIso f⟩⟩

end Geometry
end source_OrbitCells_MatrixFamily
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells.ProfileGeometry

section extension04_originalTopFace
universe uc
open CategoryTheory Limits MonoidalCategory Operad
attribute [local instance] FintypeCat.fintype
variable {W : Type uc}

/-- Every original selected input set has its actual original full-top face map. -/
def originalTopFace (P : ColoredProfile W) (S : ProfileInputSets P) :
    S ⟶ (Finset.univ : ProfileInputSets P) := homOfLE (Finset.subset_univ S)

end extension04_originalTopFace
end CategoryTheory.OperadicOrbitCells.ProfileGeometry

namespace CategoryTheory.OperadicOrbitCells.ProfileGeometry

section extension04_ProfileCellDecomposition_ProfileRelabeling
universe uc u v

open CategoryTheory Limits MonoidalCategory Operad
attribute [local instance] FintypeCat.fintype

variable {W : Type uc}
/-- The actual original finite input set admits decidable equality. -/
local instance relabelInputDecidableEq (P : ColoredProfile W) : DecidableEq P.inputs := Classical.decEq _

/-- Transport the exact original selected input positions through the profile iso. -/
def profileSubset {P Q : ColoredProfile W} (e : P ≅ Q) (S : ProfileInputSets P) : ProfileInputSets Q :=
  S.map e.hom.inputEquiv.toEmbedding

/-- Selected input membership keeps the same original position under the input bijection. -/
theorem profileSubset_mem {P Q : ColoredProfile W} (e : P ≅ Q) (S : ProfileInputSets P) (i : P.inputs) :
    e.hom.inputEquiv i ∈ profileSubset e S ↔ i ∈ S := by
  simp only [profileSubset, Finset.mem_map_equiv, Equiv.symm_apply_apply]

/-- The entire original input set is transported to the entire original input set. -/
theorem profileSubset_univ {P Q : ColoredProfile W} (e : P ≅ Q) :
    profileSubset e Finset.univ = Finset.univ := by
  apply Finset.ext
  intro i
  simp only [profileSubset, Finset.mem_map_equiv, Finset.mem_univ]

/-- Every original proper face remains a proper face under the same input bijection. -/
theorem profileSubset_punctured {P Q : ColoredProfile W} (e : P ≅ Q)
    (S : ProfilePuncturedInputSets P) : profileSubset e S.1 ≠ Finset.univ := by
  intro h
  apply S.2
  apply Finset.eq_univ_iff_forall.mpr
  intro i
  exact (profileSubset_mem e S.1 i).mp (h.symm ▸ Finset.mem_univ _)

/-- Pull back precisely the original selected input positions through the original input bijection. -/
def profileSubsetPreimage {P Q : ColoredProfile W} (e : P ≅ Q) (T : ProfileInputSets Q) : ProfileInputSets P :=
  T.map e.hom.inputEquiv.symm.toEmbedding

/-- The actual original subset is recovered after inverse input relabeling. -/
theorem profileSubset_preimage {P Q : ColoredProfile W} (e : P ≅ Q) (T : ProfileInputSets Q) :
    profileSubset e (profileSubsetPreimage e T) = T := by
  apply Finset.ext
  intro i
  simp only [profileSubset, profileSubsetPreimage, Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]

/-- Inverse input relabeling retains every actual original proper face. -/
theorem profileSubsetPreimage_punctured {P Q : ColoredProfile W} (e : P ≅ Q)
    (T : ProfilePuncturedInputSets Q) : profileSubsetPreimage e T.1 ≠ Finset.univ := by
  intro h
  apply T.2
  exact (profileSubset_preimage e T.1).symm.trans
    ((congrArg (profileSubset e) h).trans (profileSubset_univ e))

/-- The original subset-poset functor keeps the actual original input bijection. -/
def profileSubsetFunctor {P Q : ColoredProfile W} (e : P ≅ Q) : ProfileInputSets P ⥤ ProfileInputSets Q :=
  (show Monotone (profileSubset e) from fun _ _ h => Finset.map_subset_map.mpr h).functor

/-- The actual proper-face functor is induced by the same original input bijection. -/
def profilePuncturedSubsetFunctor {P Q : ColoredProfile W} (e : P ≅ Q) :
    ProfilePuncturedInputSets P ⥤ ProfilePuncturedInputSets Q where
  obj S := ⟨profileSubset e S.1, profileSubset_punctured e S⟩
  map f := homOfLE (Finset.map_subset_map.mpr (leOfHom f))

/-- The actual original input bijection and every original color/coordinate
map form a genuine marked-input isomorphism at each original face. -/
def profileInputVertexIso {P Q : ColoredProfile W} (e : P ≅ Q) (S : ProfileInputSets P) :
    (originalInputCube P).obj S ≅ (originalInputCube Q).obj (profileSubset e S) :=
  FiniteFamily.isoOfComponents e.hom.inputEquiv (fun i => eqToIso (Prod.ext
    (by
      change inputCoordinate P S i = inputCoordinate Q (profileSubset e S) (e.hom.inputEquiv i)
      unfold inputCoordinate
      simp only [profileSubset, Finset.mem_map_equiv]
      exact (congrArg (fun j : P.inputs => if j ∈ S then (Finset.univ : FiniteCube.Index 1) else ∅)
        (e.hom.inputEquiv.symm_apply_apply i)).symm)
    (congrArg Discrete.mk (e.hom.inputColor_eq i))))

/-- Every original vertex comparison keeps the actual original input bijection. -/
theorem profileInputVertexIso_inputs {P Q : ColoredProfile W} (e : P ≅ Q) (S : ProfileInputSets P) :
    (profileInputVertexIso e S).hom.equiv = e.hom.inputEquiv := rfl

/-- Every original finite-cube face commutes with that same original vertex comparison. -/
theorem profileInputVertexIso_face {P Q : ColoredProfile W} (e : P ≅ Q)
    {S T : ProfileInputSets P} (f : S ⟶ T) :
    (originalInputCube P).map f ≫ (profileInputVertexIso e T).hom =
      (profileInputVertexIso e S).hom ≫ (originalInputCube Q).map ((profileSubsetFunctor e).map f) := by
  apply markedHom_ext
  apply Equiv.ext
  intro i
  rfl

end extension04_ProfileCellDecomposition_ProfileRelabeling
end CategoryTheory.OperadicOrbitCells.ProfileGeometry

namespace CategoryTheory.OperadicOrbitCells.ProfileGeometry

section extension04_ProfileCellDecomposition_ProfileRawRelabeling
universe uc u v

open CategoryTheory Limits MonoidalCategory Operad
attribute [local instance] FintypeCat.fintype

variable {W : Type uc}

instance profileSubsetFunctorFull {P Q : ColoredProfile W} (e : P ≅ Q) : (profileSubsetFunctor e).Full where
  map_surjective := by
    intro S T f
    have h : S ⊆ T := fun i hi => (profileSubset_mem e T i).mp
      ((leOfHom f) ((profileSubset_mem e S i).mpr hi))
    exact ⟨homOfLE h, Subsingleton.elim _ _⟩

instance profileSubsetFunctorFaithful {P Q : ColoredProfile W} (e : P ≅ Q) : (profileSubsetFunctor e).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance profileSubsetFunctorEssSurj {P Q : ColoredProfile W} (e : P ≅ Q) : (profileSubsetFunctor e).EssSurj where
  mem_essImage T := ⟨profileSubsetPreimage e T, ⟨eqToIso (profileSubset_preimage e T)⟩⟩

instance profileSubsetFunctorIsEquivalence {P Q : ColoredProfile W} (e : P ≅ Q) :
    (profileSubsetFunctor e).IsEquivalence where

instance profilePuncturedSubsetFunctorFull {P Q : ColoredProfile W} (e : P ≅ Q) :
    (profilePuncturedSubsetFunctor e).Full where
  map_surjective := by
    intro S T f
    have h : S.1 ⊆ T.1 := fun i hi => (profileSubset_mem e T.1 i).mp
      ((leOfHom f) ((profileSubset_mem e S.1 i).mpr hi))
    exact ⟨homOfLE h, Subsingleton.elim _ _⟩

instance profilePuncturedSubsetFunctorFaithful {P Q : ColoredProfile W} (e : P ≅ Q) :
    (profilePuncturedSubsetFunctor e).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance profilePuncturedSubsetFunctorEssSurj {P Q : ColoredProfile W} (e : P ≅ Q) :
    (profilePuncturedSubsetFunctor e).EssSurj where
  mem_essImage T := ⟨⟨profileSubsetPreimage e T.1, profileSubsetPreimage_punctured e T⟩,
    ⟨eqToIso (Subtype.ext (profileSubset_preimage e T.1))⟩⟩

instance profilePuncturedSubsetFunctorIsEquivalence {P Q : ColoredProfile W} (e : P ≅ Q) :
    (profilePuncturedSubsetFunctor e).IsEquivalence where

/-- Compare the actual full top vertices using the original input and color isomorphism. -/
def profileTopVertexIso {P Q : ColoredProfile W} (e : P ≅ Q) :
    (originalInputCube P).obj Finset.univ ≅ (originalInputCube Q).obj Finset.univ :=
  profileInputVertexIso e Finset.univ ≪≫ (originalInputCube Q).mapIso (eqToIso (profileSubset_univ e))

/-- The original full coordinate face commutes with the actual original
input/color map at the top, including every original empty-profile correction. -/
theorem profileInputVertexIso_top {P Q : ColoredProfile W} (e : P ≅ Q) (S : ProfileInputSets P) :
    (originalInputCube P).map (originalTopFace P S) ≫ (profileTopVertexIso e).hom =
      (profileInputVertexIso e S).hom ≫ (originalInputCube Q).map (originalTopFace Q (profileSubset e S)) := by
  apply markedHom_ext
  apply Equiv.ext
  intro i
  rfl

section Tensor

variable {C : Type u} [Category.{v} C]

/-- Every original tensor vertex and face is transported through its actual input isomorphism. -/
def profileRawCubeTensorIso (D : MarkedInputs W ⥤ C) {P Q : ColoredProfile W} (e : P ≅ Q) :
    geometryInputTensorCube D P ≅ profileSubsetFunctor e ⋙ geometryInputTensorCube D Q :=
  NatIso.ofComponents (fun S => D.mapIso (profileInputVertexIso e S)) (by
    intro S T f
    exact (D.map_comp _ _).symm.trans
      ((congrArg D.map (profileInputVertexIso_face e f)).trans (D.map_comp _ _)))

/-- Every actual proper tensor face is transported through the same input isomorphism. -/
def profileRawPuncturedTensorIso (D : MarkedInputs W ⥤ C) {P Q : ColoredProfile W} (e : P ≅ Q) :
    geometryPuncturedTensor D P ≅ profilePuncturedSubsetFunctor e ⋙ geometryPuncturedTensor D Q :=
  NatIso.ofComponents (fun S => D.mapIso (profileInputVertexIso e S.1)) (by
    intro S T f
    exact (D.map_comp _ _).symm.trans
      ((congrArg D.map (profileInputVertexIso_face e ((originalPuncturedInclusion P).map f))).trans
        (D.map_comp _ _)))

/-- The original tensor top face retains the entire original input comparison square. -/
theorem profileTensorVertex_top (D : MarkedInputs W ⥤ C) {P Q : ColoredProfile W} (e : P ≅ Q)
    (S : ProfileInputSets P) :
    D.map ((originalInputCube P).map (originalTopFace P S)) ≫ D.map (profileTopVertexIso e).hom =
      D.map (profileInputVertexIso e S).hom ≫
        D.map ((originalInputCube Q).map (originalTopFace Q (profileSubset e S))) :=
  (D.map_comp _ _).symm.trans ((congrArg D.map (profileInputVertexIso_top e S)).trans (D.map_comp _ _))

end Tensor



end extension04_ProfileCellDecomposition_ProfileRawRelabeling
end CategoryTheory.OperadicOrbitCells.ProfileGeometry

namespace CategoryTheory.OperadicOrbitCells.ProfileGeometry

section extension04_ProfileCellDecomposition_ProfileRawIsos
universe uc u v us

open CategoryTheory Limits MonoidalCategory Operad
attribute [local instance] FintypeCat.fintype

variable {W : Type uc} {C : Type u} [Category.{v} C] [HasColimitsOfSize.{us, us} C]

local instance rawProfileSmallColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

/-- Keep all original proper-face quotient legs through their actual original input isomorphism. -/
def relabeledRawBoundaryCocone (D : MarkedInputs W ⥤ C) {P Q : ColoredProfile W} (e : P ≅ Q) :
    Cocone (geometryPuncturedTensor D P) :=
  (Cocone.precompose (profileRawPuncturedTensorIso D e).hom).obj
    ((colimit.cocone (geometryPuncturedTensor D Q)).whisker (profilePuncturedSubsetFunctor e))

/-- The actual input equivalence preserves the complete original proper-face colimit. -/
def relabeledRawBoundaryIsColimit (D : MarkedInputs W ⥤ C) {P Q : ColoredProfile W} (e : P ≅ Q) :
    IsColimit (relabeledRawBoundaryCocone D e) :=
  (IsColimit.precomposeHomEquiv (profileRawPuncturedTensorIso D e)
    ((colimit.cocone (geometryPuncturedTensor D Q)).whisker (profilePuncturedSubsetFunctor e))).symm
    ((Functor.Final.isColimitWhiskerEquiv (profilePuncturedSubsetFunctor e)
      (colimit.cocone (geometryPuncturedTensor D Q))).symm (colimit.isColimit _))

/-- The original input isomorphism induces the actual original boundary-object isomorphism. -/
def profileRawBoundaryIso (D : MarkedInputs W ⥤ C) {P Q : ColoredProfile W} (e : P ≅ Q) :
    geometryInputBoundary D P ≅ geometryInputBoundary D Q :=
  (colimit.isColimit (geometryPuncturedTensor D P)).coconePointUniqueUpToIso (relabeledRawBoundaryIsColimit D e)

/-- Each original boundary quotient leg retains its actual original vertex map. -/
theorem profileRawBoundaryIso_face (D : MarkedInputs W ⥤ C) {P Q : ColoredProfile W} (e : P ≅ Q)
    (S : ProfilePuncturedInputSets P) :
    colimit.ι (geometryPuncturedTensor D P) S ≫ (profileRawBoundaryIso D e).hom =
      D.map (profileInputVertexIso e S.1).hom ≫
        colimit.ι (geometryPuncturedTensor D Q) ((profilePuncturedSubsetFunctor e).obj S) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (geometryPuncturedTensor D P))
    (relabeledRawBoundaryIsColimit D e) S

/-- The actual boundary and full top comparisons form the whole original Arrow square. -/
theorem profileRawArrow_square (D : MarkedInputs W ⥤ C) {P Q : ColoredProfile W} (e : P ≅ Q) :
    (profileRawBoundaryIso D e).hom ≫ geometryBoundaryToTop D Q =
      geometryBoundaryToTop D P ≫ D.map (profileTopVertexIso e).hom := by
  let B := geometryPuncturedTensor D P
  apply colimit.hom_ext (F := B)
  intro S
  let Sq := (profilePuncturedSubsetFunctor e).obj S
  let j := colimit.ι B S
  let m := D.map (profileInputVertexIso e S.1).hom
  have hb : j ≫ ((profileRawBoundaryIso D e).hom ≫ geometryBoundaryToTop D Q) =
      m ≫ D.map ((originalInputCube Q).map (originalTopFace Q Sq.1)) :=
    (Category.assoc j _ _).symm.trans
      ((congrArg (· ≫ geometryBoundaryToTop D Q) (profileRawBoundaryIso_face D e S)).trans
        ((Category.assoc m _ _).trans (congrArg (m ≫ ·) (geometryBoundaryToTop_face D Q Sq))))
  have ht : j ≫ (geometryBoundaryToTop D P ≫ D.map (profileTopVertexIso e).hom) =
      m ≫ D.map ((originalInputCube Q).map (originalTopFace Q Sq.1)) :=
    (Category.assoc j _ _).symm.trans
      ((congrArg (· ≫ D.map (profileTopVertexIso e).hom) (geometryBoundaryToTop_face D P S)).trans
        (profileTensorVertex_top D e S.1))
  exact hb.trans ht.symm

/-- The original full unquotiented coefficient/input profile arrow is
transported with all original tensor vertex maps and both original endpoints. -/
def profileRawArrowIso (D : MarkedInputs W ⥤ C) {P Q : ColoredProfile W} (e : P ≅ Q) :
    Arrow.mk (geometryBoundaryToTop D P) ≅ Arrow.mk (geometryBoundaryToTop D Q) :=
  Arrow.isoMk (profileRawBoundaryIso D e) (D.mapIso (profileTopVertexIso e)) (profileRawArrow_square D e)

end extension04_ProfileCellDecomposition_ProfileRawIsos
end CategoryTheory.OperadicOrbitCells.ProfileGeometry

namespace CategoryTheory.OperadicOrbitCells

section extension04_OrbitCells_ColorSupport
universe uc

open CategoryTheory Operad ProfileGeometry

attribute [local instance] FintypeCat.fintype

variable {W : Type uc}

/-- Use classical equality only to enumerate the actual original finite color support. -/
local instance supportDecidableEq : DecidableEq W := Classical.decEq _

/-- The actual finite set of colors used by the original finite input set. -/
def profileColorSupport (P : ColoredProfile W) : Finset W :=
  Finset.univ.image P.inputColor

/-- The finite family index consists precisely of the original used colors. -/
abbrev ActiveColor (P : ColoredProfile W) := {r : W // r ∈ profileColorSupport P}

/-- A color is in the original support exactly when an original input has that color. -/
theorem mem_profileColorSupport_iff (P : ColoredProfile W) (r : W) :
    r ∈ profileColorSupport P ↔ ∃ i : P.inputs, P.inputColor i = r := by
  simp only [profileColorSupport, Finset.mem_image, Finset.mem_univ, true_and]

/-- Each original supported color has a strictly positive original multiplicity. -/
theorem activeColor_multiplicity_pos (P : ColoredProfile W) (r : ActiveColor P) :
    0 < colorMultiplicity P r.1 := by
  obtain ⟨i, hi⟩ := (mem_profileColorSupport_iff P r.1).1 r.2
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨i, hi⟩⟩

/-- Positive total degree gives a genuinely nonempty original finite color family. -/
theorem activeColor_nonempty (P : ColoredProfile W) (hP : 0 < inputCount P) :
    Nonempty (ActiveColor P) := by
  obtain ⟨i⟩ : Nonempty P.inputs := Fintype.card_pos_iff.mp hP
  exact ⟨⟨P.inputColor i, (mem_profileColorSupport_iff P _).2 ⟨i, rfl⟩⟩⟩

/-- The exact original input positions decompose over their actual finite used color fibers. -/
def activeInputFiberEquiv (P : ColoredProfile W) :
    P.inputs ≃ Σ r : ActiveColor P, ColorFiber P r.1 where
  toFun i :=
    ⟨⟨P.inputColor i, (mem_profileColorSupport_iff P _).2 ⟨i, rfl⟩⟩, ⟨i, rfl⟩⟩
  invFun i := i.2.1
  left_inv _ := rfl
  right_inv i := by
    rcases i with ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    cases hi
    rfl

/-- Outside the original finite support the actual original color fiber is empty. -/
theorem colorFiber_false_of_not_active (P : ColoredProfile W) (r : W)
    (hr : r ∉ profileColorSupport P) (i : ColorFiber P r) : False :=
  hr ((mem_profileColorSupport_iff P r).2 ⟨i.1, i.2⟩)

/-- Removing only empty original fibers preserves the full original permutation group. -/
def supportFiberGroupEquiv (P : ColoredProfile W) :
    (∀ r : W, Equiv.Perm (ColorFiber P r)) ≃*
      ∀ r : ActiveColor P, Equiv.Perm (ColorFiber P r.1) where
  toFun f r := f r.1
  invFun f r := if h : r ∈ profileColorSupport P then f ⟨r, h⟩ else Equiv.refl _
  left_inv f := by
    funext r
    by_cases hr : r ∈ profileColorSupport P
    · simp only [dite_eq_left hr]
    · simp only [dite_eq_right hr]
      apply Equiv.ext
      intro i
      exact (colorFiber_false_of_not_active P r hr i).elim
  right_inv f := by
    funext r
    simp only [dite_eq_left r.2]
  map_mul' _ _ := rfl

/-- The actual finite supported family has precisely its original positive Sigma multiplicities. -/
abbrev SupportedSigmaGroup (P : ColoredProfile W) :=
  ∀ r : ActiveColor P, Equiv.Perm (Fin (colorMultiplicity P r.1))

/-- The entire original profile automorphism group is the product over its actual finite support. -/
def profileSupportedSigmaEquiv (P : ColoredProfile W) : Aut P ≃* SupportedSigmaGroup P :=
  (profileAutFiberMulEquiv P).trans (supportFiberGroupEquiv P) |>.trans
    { toFun f := fun r => colorFiberSigmaMulEquiv P r.1 (f r)
      invFun f := fun r => (colorFiberSigmaMulEquiv P r.1).symm (f r)
      left_inv f := funext (fun r => (colorFiberSigmaMulEquiv P r.1).symm_apply_apply (f r))
      right_inv f := funext (fun r => (colorFiberSigmaMulEquiv P r.1).apply_symm_apply (f r))
      map_mul' f g := funext (fun r => (colorFiberSigmaMulEquiv P r.1).map_mul (f r) (g r)) }

/-- The original finite supported family has an actual finite input enumeration. -/
def supportCount (P : ColoredProfile W) : ℕ := Fintype.card (ActiveColor P)

/-- Enumerate only the actual original used colors, keeping each original color as its label. -/
def supportEnumeration (P : ColoredProfile W) : Fin (supportCount P) ≃ ActiveColor P :=
  (Fintype.equivFin _).symm

/-- The original color attached to an actual supported-family index. -/
def supportedLabel (P : ColoredProfile W) (r : Fin (supportCount P)) : W :=
  (supportEnumeration P r).1

/-- This source enumeration is injective on the actual original colors. -/
theorem supportedLabel_injective (P : ColoredProfile W) :
    Function.Injective (supportedLabel P) :=
  Subtype.val_injective.comp (supportEnumeration P).injective

/-- Reindexing one actual supported color recovers the same original color. -/
theorem supportedLabel_enumeration_symm (P : ColoredProfile W) (r : ActiveColor P) :
    supportedLabel P ((supportEnumeration P).symm r) = r.1 :=
  congrArg Subtype.val ((supportEnumeration P).apply_symm_apply r)

/-- The tuple entry is the actual original multiplicity of the original supported color. -/
def supportedMultiplicity (P : ColoredProfile W) (r : Fin (supportCount P)) : ℕ :=
  colorMultiplicity P (supportedLabel P r)

/-- Every entry of the original supported tuple is positive. -/
theorem supportedMultiplicity_pos (P : ColoredProfile W) (r : Fin (supportCount P)) :
    0 < supportedMultiplicity P r :=
  activeColor_multiplicity_pos P (supportEnumeration P r)

/-- The actual original input set is the expanded finite tuple of its
positive color multiplicities. -/
def supportedExpandedInputEquiv (P : ColoredProfile W) :
    P.inputs ≃ Σ r : Fin (supportCount P), Fin (supportedMultiplicity P r) :=
  (activeInputFiberEquiv P).trans
    (Equiv.sigmaCongr (supportEnumeration P).symm (fun r => by
      change ColorFiber P r.1 ≃ Fin (colorMultiplicity P
        (supportedLabel P ((supportEnumeration P).symm r)))
      rw [supportedLabel_enumeration_symm]
      exact Fintype.equivFin _))

/-- The expanded input still has the same original color at every original position. -/
theorem supportedExpandedInputEquiv_color (P : ColoredProfile W) (i : P.inputs) :
    supportedLabel P (supportedExpandedInputEquiv P i).1 = P.inputColor i :=
  supportedLabel_enumeration_symm P
    ⟨P.inputColor i, (mem_profileColorSupport_iff P _).2 ⟨i, rfl⟩⟩

end extension04_OrbitCells_ColorSupport
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells

section extension04_OrbitCells_ExpandedProfile
universe uc

open CategoryTheory Operad ProfileGeometry

attribute [local instance] FintypeCat.fintype

variable {W : Type uc}

/-- Positive total original degree makes the actual supported finite index nonempty. -/
theorem supportCount_pos (P : ColoredProfile W) (hP : 0 < inputCount P) :
    0 < supportCount P :=
  Fintype.card_pos_iff.mpr (activeColor_nonempty P hP)

/-- The supported expanded profile stays in the original palette and keeps its original output. -/
def expandedProfile (P : ColoredProfile W) : ColoredProfile W where
  inputs := FintypeCat.of (Σ r : Fin (supportCount P), Fin (supportedMultiplicity P r))
  inputColor i := supportedLabel P i.1
  outputColor := P.outputColor

/-- The exact original input/color bijection is an actual isomorphism of original profiles. -/
def originalExpandedProfileIso (P : ColoredProfile W) : P ≅ expandedProfile P :=
  asIso (show P ⟶ expandedProfile P from
    { inputEquiv := supportedExpandedInputEquiv P
      inputColor_eq i := (supportedExpandedInputEquiv_color P i).symm
      outputColor_eq := rfl })

/-- The actual color fiber of the expanded profile is its original positive tuple entry. -/
def expandedProfileFiberEquiv (P : ColoredProfile W) (r : Fin (supportCount P)) :
    ColorFiber (expandedProfile P) (supportedLabel P r) ≃ Fin (supportedMultiplicity P r) where
  toFun p := by
    rcases p with ⟨⟨s, i⟩, h⟩
    have hs : s = r := supportedLabel_injective P h
    cases hs
    exact i
  invFun i := ⟨⟨r, i⟩, rfl⟩
  left_inv p := by
    rcases p with ⟨⟨s, i⟩, h⟩
    have hs : s = r := supportedLabel_injective P h
    cases hs
    rfl
  right_inv _ := rfl

/-- The actual original tuple-entry bijection transports its whole permutation group. -/
def expandedProfileFiberPermutationEquiv (P : ColoredProfile W)
    (r : Fin (supportCount P)) :
    Equiv.Perm (ColorFiber (expandedProfile P) (supportedLabel P r)) ≃*
      Equiv.Perm (Fin (supportedMultiplicity P r)) :=
  { (expandedProfileFiberEquiv P r).permCongr with
    map_mul' := fun f g => ((expandedProfileFiberEquiv P r).permCongr_trans g f).symm }

/-- The actual supported expanded input tuple admits every original product permutation. -/
def expandedProfileProductAut (P : ColoredProfile W)
    (f : MultiplicityGroup (supportedMultiplicity P)) : Aut (expandedProfile P) :=
  Aut.of (asIso (show expandedProfile P ⟶ expandedProfile P from
    { inputEquiv := Equiv.sigmaCongrRight f
      inputColor_eq _ := rfl
      outputColor_eq := rfl }))

/-- Restrict the actual original expanded profile automorphism to one original tuple entry. -/
def expandedProfileAutComponent (P : ColoredProfile W) (g : Aut (expandedProfile P))
    (r : Fin (supportCount P)) : Equiv.Perm (Fin (supportedMultiplicity P r)) :=
  expandedProfileFiberPermutationEquiv P r
    (profileAutFiberPermutation (expandedProfile P) g (supportedLabel P r))

/-- Every actual product permutation is recovered on the same original tuple entry. -/
theorem expandedProfileProductAut_component (P : ColoredProfile W)
    (f : MultiplicityGroup (supportedMultiplicity P)) (r : Fin (supportCount P)) :
    expandedProfileAutComponent P (expandedProfileProductAut P f) r = f r := rfl

/-- The actual expanded profile group is precisely the displayed finite product of Sigmas. -/
def expandedProfileAutEquiv (P : ColoredProfile W) :
    Aut (expandedProfile P) ≃* MultiplicityGroup (supportedMultiplicity P) where
  toFun := expandedProfileAutComponent P
  invFun := expandedProfileProductAut P
  left_inv g := by
    classical
    apply (profileAutFiberMulEquiv (expandedProfile P)).injective
    funext w
    by_cases hw : w ∈ Set.range (supportedLabel P)
    · obtain ⟨r, rfl⟩ := hw
      apply (expandedProfileFiberPermutationEquiv P r).injective
      exact expandedProfileProductAut_component P (expandedProfileAutComponent P g) r
    · apply Equiv.ext
      rintro ⟨⟨r, i⟩, hr⟩
      exact (hw ⟨r, hr⟩).elim
  right_inv f := by
    funext r
    apply Equiv.ext
    intro i
    rfl
  map_mul' f g := by
    funext r
    have h := congrFun ((profileAutFiberMulEquiv (expandedProfile P)).map_mul f g)
      (supportedLabel P r)
    exact (congrArg (expandedProfileFiberPermutationEquiv P r) h).trans
      ((expandedProfileFiberPermutationEquiv P r).map_mul _ _)

/-- The original full profile group is the product of its actual positive supported tuple. -/
def originalProfileFiniteSigmaEquiv (P : ColoredProfile W) :
    Aut P ≃* MultiplicityGroup (supportedMultiplicity P) :=
  (Aut.autMulEquivOfIso (originalExpandedProfileIso P)).trans (expandedProfileAutEquiv P)

end extension04_OrbitCells_ExpandedProfile
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells

section extension04_OrbitCells_GeometryFunctorial
universe uc u v us

open CategoryTheory Limits MonoidalCategory Operad ProfileGeometry

attribute [local instance] FintypeCat.fintype

variable {W : Type uc} {C : Type u} [Category.{v} C]
  [HasColimitsOfSize.{us, us} C]

local instance functorialSmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

/-- The actual transformation on the unchanged original proper-face diagram. -/
def originalBoundaryTransformation {D E : MarkedInputs W ⥤ C} (a : D ⟶ E)
    (P : ColoredProfile W) : geometryPuncturedTensor D P ⟶ geometryPuncturedTensor E P :=
  Functor.whiskerLeft (originalPuncturedInclusion P ⋙ originalInputCube P) a

/-- The induced map is the actual original proper-face colimit map. -/
def originalBoundaryMap {D E : MarkedInputs W ⥤ C} (a : D ⟶ E)
    (P : ColoredProfile W) : geometryInputBoundary D P ⟶ geometryInputBoundary E P :=
  colimMap (originalBoundaryTransformation a P)

/-- Every original face retains its actual original transformation component. -/
@[reassoc]
theorem originalBoundaryMap_face {D E : MarkedInputs W ⥤ C} (a : D ⟶ E)
    (P : ColoredProfile W) (S : ProfilePuncturedInputSets P) :
    colimit.ι (geometryPuncturedTensor D P) S ≫ originalBoundaryMap a P =
      a.app ((originalInputCube P).obj S.1) ≫
        colimit.ι (geometryPuncturedTensor E P) S :=
  ι_colimMap (originalBoundaryTransformation a P) S

/-- The complete original source and target transformation preserves its original arrow. -/
theorem originalBoundaryMap_square {D E : MarkedInputs W ⥤ C} (a : D ⟶ E)
    (P : ColoredProfile W) :
    originalBoundaryMap a P ≫ geometryBoundaryToTop E P =
      geometryBoundaryToTop D P ≫ a.app ((originalInputCube P).obj Finset.univ) := by
  apply colimit.hom_ext
  intro S
  let t := (originalInputCube P).map (homOfLE (Finset.subset_univ S.1))
  have hL : colimit.ι (geometryPuncturedTensor D P) S ≫
      (originalBoundaryMap a P ≫ geometryBoundaryToTop E P) =
      a.app ((originalInputCube P).obj S.1) ≫ E.map t :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ geometryBoundaryToTop E P) (originalBoundaryMap_face a P S)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (a.app ((originalInputCube P).obj S.1) ≫ ·)
            (geometryBoundaryToTop_face E P S))))
  have hR : colimit.ι (geometryPuncturedTensor D P) S ≫
      (geometryBoundaryToTop D P ≫ a.app ((originalInputCube P).obj Finset.univ)) =
      D.map t ≫ a.app ((originalInputCube P).obj Finset.univ) :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ a.app ((originalInputCube P).obj Finset.univ))
        (geometryBoundaryToTop_face D P S))
  exact hL.trans ((a.naturality t).symm.trans hR.symm)

/-- The full original transformation commutes with every original boundary permutation. -/
theorem originalBoundaryMap_aut {D E : MarkedInputs W ⥤ C} (a : D ⟶ E)
    (P : ColoredProfile W) (g : Aut P) :
    geometryAutMap D P g ≫ originalBoundaryMap a P =
      originalBoundaryMap a P ≫ geometryAutMap E P g := by
  apply colimit.hom_ext
  intro S
  let Sg := (profileAutPunctured P g).obj S
  have hn := a.naturality (profileAutInputVertexIso P g S.1).hom
  have hL : colimit.ι (geometryPuncturedTensor D P) S ≫
      (geometryAutMap D P g ≫ originalBoundaryMap a P) =
      (D.map (profileAutInputVertexIso P g S.1).hom ≫
        a.app ((originalInputCube P).obj Sg.1)) ≫
        colimit.ι (geometryPuncturedTensor E P) Sg :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ originalBoundaryMap a P) (geometryAutMap_face D P g S)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (D.map (profileAutInputVertexIso P g S.1).hom ≫ ·)
            (originalBoundaryMap_face a P Sg)).trans (Category.assoc _ _ _).symm)))
  have hR : colimit.ι (geometryPuncturedTensor D P) S ≫
      (originalBoundaryMap a P ≫ geometryAutMap E P g) =
      (a.app ((originalInputCube P).obj S.1) ≫
        E.map (profileAutInputVertexIso P g S.1).hom) ≫
        colimit.ι (geometryPuncturedTensor E P) Sg :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ geometryAutMap E P g) (originalBoundaryMap_face a P S)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (a.app ((originalInputCube P).obj S.1) ≫ ·)
            (geometryAutMap_face E P g S)).trans (Category.assoc _ _ _).symm)))
  exact hL.trans ((congrArg (· ≫ colimit.ι (geometryPuncturedTensor E P) Sg) hn).trans
    hR.symm)

omit [HasColimitsOfSize.{us, us} C] in
/-- The original top transformation preserves the actual original full-input action. -/
theorem originalTopMap_aut {D E : MarkedInputs W ⥤ C} (a : D ⟶ E)
    (P : ColoredProfile W) (g : Aut P) :
    (geometryInputTopRepresentation D P g).asHom ≫
        a.app ((originalInputCube P).obj Finset.univ) =
      a.app ((originalInputCube P).obj Finset.univ) ≫
        (geometryInputTopRepresentation E P g).asHom :=
  a.naturality (originalInputTopHom P g).asIso.hom

/-- The original action is a complete action on the actual original whole arrow. -/
def rawGeometryArrowAction (D : MarkedInputs W ⥤ C) (P : ColoredProfile W) :
    Action (Arrow C) (Aut P) :=
  (Action.functorCategoryEquivalence (Arrow C) (Aut P)).inverse.obj
    (CategoryTheory.naturalArrowFunctor (geometryBoundaryTopTransformation D P))

/-- The actual original finite-profile action arrow is functorial in the full source diagram. -/
def rawGeometryActionFunctor (P : ColoredProfile W) :
    (MarkedInputs W ⥤ C) ⥤ Action (Arrow C) (Aut P) where
  obj D := rawGeometryArrowAction D P
  map a :=
    { hom := Arrow.homMk (originalBoundaryMap a P)
        (a.app ((originalInputCube P).obj Finset.univ)) (originalBoundaryMap_square a P)
      comm g := Arrow.hom_ext _ _ (originalBoundaryMap_aut a P g) (originalTopMap_aut a P g) }
  map_id D := by
    apply Action.Hom.ext
    apply Arrow.hom_ext
    · exact (colim (J := ProfilePuncturedInputSets P) (C := C)).map_id
        (geometryPuncturedTensor D P)
    · rfl
  map_comp a b := by
    apply Action.Hom.ext
    apply Arrow.hom_ext
    · exact (colim (J := ProfilePuncturedInputSets P) (C := C)).map_comp
        (originalBoundaryTransformation a P) (originalBoundaryTransformation b P)
    · rfl

/-- The actual original diagram iso gives its complete source/target action Arrow iso. -/
def rawGeometryActionIso {D E : MarkedInputs W ⥤ C} (e : D ≅ E)
    (P : ColoredProfile W) : rawGeometryArrowAction D P ≅ rawGeometryArrowAction E P :=
  (rawGeometryActionFunctor P).mapIso e

end extension04_OrbitCells_GeometryFunctorial
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells

section extension04_OrbitCells_GroupChange
universe ug uh u v

open CategoryTheory Limits MonoidalCategory ProfileGeometry

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {G : Type ug} [Group G] {H : Type uh} [Group H]

/-- Restriction keeps the full original coefficient-action tensor diagram. -/
theorem coefficientSourceFunctor_restrict (e : G ≃* H) (Y B : Action C H) :
    coefficientSourceFunctor ((Action.res C e.toMonoidHom).obj Y)
        ((Action.res C e.toMonoidHom).obj B) =
      e.toSingleObjEquiv.functor ⋙ coefficientSourceFunctor Y B := rfl

/-- The original complete coefficient arrow restricts through the same original group functor. -/
theorem coefficientArrowFunctor_restrict (e : G ≃* H) (Y : Action C H)
    {B T : Action C H} (p : B ⟶ T) :
    CategoryTheory.naturalArrowFunctor (coefficientTransformation ((Action.res C e.toMonoidHom).obj Y)
        ((Action.res C e.toMonoidHom).map p)) =
      e.toSingleObjEquiv.functor ⋙ CategoryTheory.naturalArrowFunctor (coefficientTransformation Y p) := rfl

variable [HasColimitsOfShape (SingleObj G) C] [HasColimitsOfShape (SingleObj H) C]

/-- Both original orbit projections are retained by whiskering the original whole Arrow cocone. -/
def restrictedCoefficientOrbitCocone (e : G ≃* H) (Y : Action C H)
    {B T : Action C H} (p : B ⟶ T) :
    Cocone (CategoryTheory.naturalArrowFunctor (coefficientTransformation
      ((Action.res C e.toMonoidHom).obj Y) ((Action.res C e.toMonoidHom).map p))) :=
  (coefficientOrbitCocone Y p).whisker e.toSingleObjEquiv.functor

/-- The actual group equivalence preserves the full original Arrow colimit. -/
def restrictedCoefficientOrbitIsColimit (e : G ≃* H) (Y : Action C H)
    {B T : Action C H} (p : B ⟶ T) :
    IsColimit (restrictedCoefficientOrbitCocone e Y p) :=
  (Functor.Final.isColimitWhiskerEquiv e.toSingleObjEquiv.functor
    (coefficientOrbitCocone Y p)).symm (coefficientOrbitIsColimit Y p)

/-- The complete original coefficient orbit Arrow is unchanged through the actual group iso. -/
def coefficientOrbitGroupChangeIso (e : G ≃* H) (Y : Action C H)
    {B T : Action C H} (p : B ⟶ T) :
    coefficientOrbitArrow ((Action.res C e.toMonoidHom).obj Y)
        ((Action.res C e.toMonoidHom).map p) ≅ coefficientOrbitArrow Y p :=
  IsColimit.coconePointUniqueUpToIso
    (coefficientOrbitIsColimit ((Action.res C e.toMonoidHom).obj Y)
      ((Action.res C e.toMonoidHom).map p))
    (restrictedCoefficientOrbitIsColimit e Y p)

/-- The actual whole original quotient cofan survives the same group-change Arrow iso. -/
theorem coefficientOrbitGroupChangeIso_cofan (e : G ≃* H) (Y : Action C H)
    {B T : Action C H} (p : B ⟶ T) :
    (coefficientOrbitCocone ((Action.res C e.toMonoidHom).obj Y)
        ((Action.res C e.toMonoidHom).map p)).ι.app (SingleObj.star G) ≫
        (coefficientOrbitGroupChangeIso e Y p).hom =
      (coefficientOrbitCocone Y p).ι.app (SingleObj.star H) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coefficientOrbitIsColimit ((Action.res C e.toMonoidHom).obj Y)
      ((Action.res C e.toMonoidHom).map p))
    (restrictedCoefficientOrbitIsColimit e Y p) (SingleObj.star G)

end extension04_OrbitCells_GroupChange
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells

section extension04_OrbitCells_CoefficientChange
universe ug u v

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {G : Type ug} [Group G] [HasColimitsOfShape (SingleObj G) C]

/-- The actual whole coefficient tensor arrow is unchanged by an equivariant coefficient iso. -/
def coefficientTensorArrowIso {Y Yprime : Action C G} (e : Y ≅ Yprime)
    {B T : Action C G} (p : B ⟶ T) :
    Arrow.mk (Y ◁ p) ≅ Arrow.mk (Yprime ◁ p) :=
  Arrow.isoMk (tensorIso e (Iso.refl B)) (tensorIso e (Iso.refl T)) (by
    change (e.hom ⊗ₘ 𝟙 B) ≫ (Yprime ◁ p) = (Y ◁ p) ≫ (e.hom ⊗ₘ 𝟙 T)
    rw [← id_tensorHom Yprime p, ← id_tensorHom Y p,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, Category.id_comp, Category.comp_id])

/-- Both original actual orbit projections survive the same coefficient-action iso. -/
def coefficientOrbitCoefficientIso {Y Yprime : Action C G} (e : Y ≅ Yprime)
    {B T : Action C G} (p : B ⟶ T) :
    coefficientOrbitArrow Y p ≅ coefficientOrbitArrow Yprime p :=
  (Action.coinvariantsFunctor (C := C) G).mapArrow.mapIso (coefficientTensorArrowIso e p)

end extension04_OrbitCells_CoefficientChange
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells.ProfileReindex

section extension04_OrbitCells_ProfileReindex
universe uc u v us

open CategoryTheory Limits MonoidalCategory Operad
open ProfileGeometry

attribute [local instance] FintypeCat.fintype

variable {W : Type uc}

/-- The inverse original profile map has the inverse of the same original input bijection. -/
theorem profileIso_inverse_input {P Q : ColoredProfile W} (e : P ≅ Q) :
    e.inv.inputEquiv = e.hom.inputEquiv.symm := by
  apply Equiv.ext
  intro i
  have h := congrArg (fun f : P ⟶ P => f.inputEquiv (e.hom.inputEquiv.symm i))
    e.hom_inv_id
  change e.inv.inputEquiv (e.hom.inputEquiv (e.hom.inputEquiv.symm i)) =
    e.hom.inputEquiv.symm i at h
  simpa only [Equiv.apply_symm_apply] using h

/-- Conjugation retains the same actual original input permutation through the profile bijection. -/
theorem conjugateProfileAut_input {P Q : ColoredProfile W} (e : P ≅ Q) (g : Aut P)
    (i : P.inputs) :
    ((Aut.autMulEquivOfIso e) g).asIso.hom.inputEquiv (e.hom.inputEquiv i) =
      e.hom.inputEquiv (g.asIso.hom.inputEquiv i) := by
  change e.hom.inputEquiv (g.asIso.hom.inputEquiv
    (e.inv.inputEquiv (e.hom.inputEquiv i))) = _
  rw [profileIso_inverse_input]
  simp only [Equiv.symm_apply_apply]

/-- Relabelling and the original automorphism carry the same original selected input positions. -/
theorem profileSubset_aut {P Q : ColoredProfile W} (e : P ≅ Q) (g : Aut P)
    (S : ProfileInputSets P) :
    profileSubset e (profileAutSubset P g S) =
      profileAutSubset Q ((Aut.autMulEquivOfIso e) g) (profileSubset e S) := by
  unfold profileSubset profileAutSubset
  rw [Finset.map_map, Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro i
  exact (conjugateProfileAut_input e g i).symm

/-- The full original marked-input relabelling and permutation maps form the same square. -/
theorem profileAutVertex_relabel {P Q : ColoredProfile W} (e : P ≅ Q) (g : Aut P)
    (S : ProfileInputSets P) :
    (profileAutInputVertexIso P g S).hom ≫
        (profileInputVertexIso e (profileAutSubset P g S)).hom ≫
        (originalInputCube Q).map (eqToHom (profileSubset_aut e g S)) =
      (profileInputVertexIso e S).hom ≫
        (profileAutInputVertexIso Q ((Aut.autMulEquivOfIso e) g) (profileSubset e S)).hom := by
  apply markedHom_ext
  apply Equiv.ext
  intro i
  exact (conjugateProfileAut_input e g i).symm

/-- Both original top permutations commute with the same original full profile top map. -/
theorem profileTopAut_relabel {P Q : ColoredProfile W} (e : P ≅ Q) (g : Aut P) :
    (originalInputTopHom P g).asIso.hom ≫ (profileTopVertexIso e).hom =
      (profileTopVertexIso e).hom ≫
        (originalInputTopHom Q ((Aut.autMulEquivOfIso e) g)).asIso.hom := by
  apply markedHom_ext
  apply Equiv.ext
  intro i
  exact (conjugateProfileAut_input e g i).symm

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{us, us} C]

local instance reindexSmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

/-- The actual original raw boundary comparison intertwines both original automorphism actions. -/
theorem profileRawBoundaryIso_aut (D : MarkedInputs W ⥤ C)
    {P Q : ColoredProfile W} (e : P ≅ Q) (g : Aut P) :
    geometryAutMap D P g ≫ (profileRawBoundaryIso D e).hom =
      (profileRawBoundaryIso D e).hom ≫ geometryAutMap D Q ((Aut.autMulEquivOfIso e) g) := by
  let B := geometryPuncturedTensor D P
  let Bq := geometryPuncturedTensor D Q
  apply colimit.hom_ext (F := B)
  intro S
  let Sg := (profileAutPunctured P g).obj S
  let Sq := (profilePuncturedSubsetFunctor e).obj S
  let T₁ := (profilePuncturedSubsetFunctor e).obj Sg
  let T₂ := (profileAutPunctured Q ((Aut.autMulEquivOfIso e) g)).obj Sq
  have hT : T₁ = T₂ := Subtype.ext (profileSubset_aut e g S.1)
  let q : T₁ ⟶ T₂ := eqToHom hT
  have hq : colimit.ι Bq T₁ = Bq.map q ≫ colimit.ι Bq T₂ := (colimit.w Bq q).symm
  have hm : (D.map (profileAutInputVertexIso P g S.1).hom ≫
      D.map (profileInputVertexIso e Sg.1).hom) ≫ Bq.map q =
      D.map (profileInputVertexIso e S.1).hom ≫
        D.map (profileAutInputVertexIso Q ((Aut.autMulEquivOfIso e) g) Sq.1).hom := by
    have h := congrArg D.map (profileAutVertex_relabel e g S.1)
    have hqcube : (originalPuncturedInclusion Q).map q =
        eqToHom (profileSubset_aut e g S.1) := Subsingleton.elim _ _
    change (D.map (profileAutInputVertexIso P g S.1).hom ≫
        D.map (profileInputVertexIso e Sg.1).hom) ≫
        D.map ((originalInputCube Q).map ((originalPuncturedInclusion Q).map q)) = _
    rw [hqcube]
    exact (Category.assoc _ _ _).trans (by
      simpa only [D.map_comp, Sg, Sq, T₂, profileAutPunctured,
        profilePuncturedSubsetFunctor, originalPuncturedInclusion] using h)
  have hL : colimit.ι B S ≫
      (geometryAutMap D P g ≫ (profileRawBoundaryIso D e).hom) =
      (D.map (profileAutInputVertexIso P g S.1).hom ≫
        D.map (profileInputVertexIso e Sg.1).hom) ≫ colimit.ι Bq T₁ :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (profileRawBoundaryIso D e).hom) (geometryAutMap_face D P g S)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (D.map (profileAutInputVertexIso P g S.1).hom ≫ ·)
            (profileRawBoundaryIso_face D e Sg)).trans (Category.assoc _ _ _).symm)))
  have hR : colimit.ι B S ≫
      ((profileRawBoundaryIso D e).hom ≫ geometryAutMap D Q ((Aut.autMulEquivOfIso e) g)) =
      (D.map (profileInputVertexIso e S.1).hom ≫
        D.map (profileAutInputVertexIso Q ((Aut.autMulEquivOfIso e) g) Sq.1).hom) ≫
          colimit.ι Bq T₂ :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ geometryAutMap D Q ((Aut.autMulEquivOfIso e) g))
        (profileRawBoundaryIso_face D e S)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (D.map (profileInputVertexIso e S.1).hom ≫ ·)
            (geometryAutMap_face D Q ((Aut.autMulEquivOfIso e) g) Sq)).trans
              (Category.assoc _ _ _).symm)))
  exact hL.trans ((congrArg ((D.map (profileAutInputVertexIso P g S.1).hom ≫
      D.map (profileInputVertexIso e Sg.1).hom) ≫ ·) hq).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ colimit.ι Bq T₂) hm).trans hR.symm)))

omit [HasColimitsOfSize.{us, us} C] in
/-- The actual original raw top comparison intertwines both original top representations. -/
theorem profileRawTopIso_aut (D : MarkedInputs W ⥤ C)
    {P Q : ColoredProfile W} (e : P ≅ Q) (g : Aut P) :
    (geometryInputTopRepresentation D P g).asHom ≫ D.map (profileTopVertexIso e).hom =
      D.map (profileTopVertexIso e).hom ≫
        (geometryInputTopRepresentation D Q ((Aut.autMulEquivOfIso e) g)).asHom := by
  have h := congrArg D.map (profileTopAut_relabel e g)
  change D.map (originalInputTopHom P g).asIso.hom ≫ D.map (profileTopVertexIso e).hom =
    D.map (profileTopVertexIso e).hom ≫
      D.map (originalInputTopHom Q ((Aut.autMulEquivOfIso e) g)).asIso.hom
  simpa only [D.map_comp] using h

/-- The full original profile Arrow iso is the actual source and target action iso. -/
def rawProfileActionIso (D : MarkedInputs W ⥤ C) {P Q : ColoredProfile W} (e : P ≅ Q) :
    rawGeometryArrowAction D P ≅
      (Action.res (Arrow C) (Aut.autMulEquivOfIso e).toMonoidHom).obj
        (rawGeometryArrowAction D Q) :=
  Action.mkIso (profileRawArrowIso D e) (by
    intro g
    apply Arrow.hom_ext
    · exact profileRawBoundaryIso_aut D e g
    · exact profileRawTopIso_aut D e g)

end extension04_OrbitCells_ProfileReindex
end CategoryTheory.OperadicOrbitCells.ProfileReindex

namespace CategoryTheory.OperadicOrbitCells

section extension04_OrbitCells_ProfileOrbitReindex
universe uc u v us

open CategoryTheory Limits MonoidalCategory Operad
open ProfileGeometry ProfileReindex

variable {W : Type uc} {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasColimitsOfSize.{us, us} C]

local instance profileOrbitSmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J
local instance profileOrbitAutColimits (P : ColoredProfile W) :
    HasColimitsOfShape (SingleObj (Aut P)) C :=
  HasColimitsOfShape.of_essentiallySmall C _

/-- Transport the same original arbitrary coefficient through the full original group iso. -/
def profileCoefficientTransport {P Q : ColoredProfile W} (e : P ≅ Q)
    (Y : Action C (Aut P)) : Action C (Aut Q) :=
  (Action.res C (Aut.autMulEquivOfIso e).symm.toMonoidHom).obj Y

/-- Both original raw orbit objects and the entire actual Arrow survive
profile input relabelling. -/
def profileRawOrbitReindexIso (D : MarkedInputs W ⥤ C) {P Q : ColoredProfile W}
    (e : P ≅ Q) (Y : Action C (Aut P)) :
    coefficientOrbitArrow Y (Action.actionUnderlyingHom (rawGeometryArrowAction D P)) ≅
      coefficientOrbitArrow (profileCoefficientTransport e Y)
        (Action.actionUnderlyingHom (rawGeometryArrowAction D Q)) := by
  let eg := Aut.autMulEquivOfIso e
  let Yq := profileCoefficientTransport e Y
  let A := rawGeometryArrowAction D Q
  let r := Action.actionUnderlyingHom
    ((Action.res (Arrow C) eg.toMonoidHom).obj A)
  let ey : (Action.res C eg.toMonoidHom).obj Yq ≅ Y :=
    (Action.resEquiv C eg).counitIso.app Y
  exact coefficientOrbitActionIso Y (ProfileReindex.rawProfileActionIso D e) ≪≫
    coefficientOrbitCoefficientIso ey.symm r ≪≫
      coefficientOrbitGroupChangeIso eg Yq (Action.actionUnderlyingHom A)

variable [SymmetricCategory C] [MonoidalClosed C]

/-- The actual complete coefficient-weighted iterated PP orbit keeps the original profile map. -/
def profileIteratedOrbitReindexIso {X Xprime : W → C} (x : X ⟶ Xprime)
    {P Q : ColoredProfile W} (e : P ≅ Q) (Y : Action C (Aut P)) :
    profileIteratedOrbitArrow x P Y ≅
      profileIteratedOrbitArrow x Q (profileCoefficientTransport e Y) :=
  (profileOrbitPushoutProductIso x P Y).symm ≪≫
    profileRawOrbitReindexIso (inputTensorDiagram x) e Y ≪≫
      profileOrbitPushoutProductIso x Q (profileCoefficientTransport e Y)

end extension04_OrbitCells_ProfileOrbitReindex
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells

section extension04_OrbitCells_Recolor
universe ur uw u v

open CategoryTheory Limits MonoidalCategory Operad ProfileGeometry

variable {R : Type ur} {W : Type uw}

/-- Recolor only the original inputs while retaining an independently specified original output. -/
def recoloredProfile (c : R → W) (d : W) (P : ColoredProfile R) : ColoredProfile W where
  inputs := P.inputs
  inputColor := c ∘ P.inputColor
  outputColor := d

/-- An injective original color map preserves the entire original input automorphism group. -/
def recoloredProfileAutEquiv (c : R → W) (hc : Function.Injective c)
    (d : W) (P : ColoredProfile R) : Aut P ≃* Aut (recoloredProfile c d P) where
  toFun g := Aut.of (asIso (show recoloredProfile c d P ⟶ recoloredProfile c d P from
    { inputEquiv := g.asIso.hom.inputEquiv
      inputColor_eq i := congrArg c (g.asIso.hom.inputColor_eq i)
      outputColor_eq := rfl }))
  invFun g := Aut.of (asIso (show P ⟶ P from
    { inputEquiv := g.asIso.hom.inputEquiv
      inputColor_eq i := hc (g.asIso.hom.inputColor_eq i)
      outputColor_eq := rfl }))
  left_inv _ := by
    apply Aut.ext
    apply Iso.ext
    apply ColoredProfile.Hom.ext
    rfl
  right_inv _ := by
    apply Aut.ext
    apply Iso.ext
    apply ColoredProfile.Hom.ext
    rfl
  map_mul' _ _ := by
    apply Aut.ext
    apply Iso.ext
    apply ColoredProfile.Hom.ext
    rfl

/-- Change only the original input color, retaining its actual one-slot coordinate. -/
def recolorMarkedColor (c : R → W) : MarkedColor R ⥤ MarkedColor W where
  obj M := (M.1, Discrete.mk (c M.2.as))
  map f := (f.1, Discrete.eqToHom (congrArg c (Discrete.eq_of_hom f.2)))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The original finite input bijections are retained under color relabelling. -/
def recolorMarkedInputs (c : R → W) : MarkedInputs R ⥤ MarkedInputs W :=
  FiniteFamily.map (recolorMarkedColor c)

attribute [local instance] FintypeCat.fintype

/-- The full original subset cube is unchanged under the actual input-color relabelling. -/
theorem recoloredInputCube (c : R → W) (d : W) (P : ColoredProfile R) :
    originalInputCube P ⋙ recolorMarkedInputs c = originalInputCube (recoloredProfile c d P) := by
  refine Functor.hext (fun _ => rfl) (fun S T f => ?_)
  apply heq_of_eq
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    rfl

/-- The actual full original permutation is unchanged by input recoloring. -/
theorem recoloredAutSubset (c : R → W) (hc : Function.Injective c)
    (d : W) (P : ColoredProfile R) (g : Aut P) (S : ProfileInputSets P) :
    profileAutSubset (recoloredProfile c d P) ((recoloredProfileAutEquiv c hc d P) g) S =
      profileAutSubset P g S := rfl

/-- The original marked-input group map is carried through its actual color map. -/
theorem recoloredAutVertex (c : R → W) (hc : Function.Injective c)
    (d : W) (P : ColoredProfile R) (g : Aut P) (S : ProfileInputSets P) :
    (recolorMarkedInputs c).map (profileAutInputVertexIso P g S).hom =
      (profileAutInputVertexIso (recoloredProfile c d P)
        ((recoloredProfileAutEquiv c hc d P) g) S).hom := by
  apply markedHom_ext
  rfl

/-- The original full-top input map is carried through the same original color map. -/
theorem recoloredTopAut (c : R → W) (hc : Function.Injective c)
    (d : W) (P : ColoredProfile R) (g : Aut P) :
    (recolorMarkedInputs c).map (originalInputTopHom P g).asIso.hom =
      (originalInputTopHom (recoloredProfile c d P)
        ((recoloredProfileAutEquiv c hc d P) g)).asIso.hom := by
  apply markedHom_ext
  apply Equiv.ext
  intro i
  rfl

variable {C : Type u} [Category.{v} C]

private theorem pi_hom_heq_apply {A B A' B' : R → C} {f : A ⟶ B} {g : A' ⟶ B'}
    (hA : A = A') (hB : B = B') (hf : HEq f g) (r : R) : HEq (f r) (g r) := by
  subst A'
  subst B'
  exact heq_of_eq (congrArg (fun h => h r) (eq_of_heq hf))

/-- A fixed original color evaluates exactly the original one-slot coordinate map. -/
theorem markedCarrier_map_coordinate {X Xprime : W → C} (x : X ⟶ Xprime)
    {S T : FiniteCube.Index 1} (f : S ⟶ T) (r : W) :
    (markedInputCarrier x).map (show (S, Discrete.mk r) ⟶ (T, Discrete.mk r) from
      (f, 𝟙 (Discrete.mk r))) =
      (FiniteCube.coordinateCube (C := W → C) x (0 : Fin 1)).map f r := by
  change ((FiniteCube.coordinateCube (C := W → C) x (0 : Fin 1)).map f r) ≫
    (Discrete.functor ((FiniteCube.coordinateCube (C := W → C) x (0 : Fin 1)).obj T)).map
      (𝟙 (Discrete.mk r)) = _
  exact (congrArg (((FiniteCube.coordinateCube (C := W → C) x (0 : Fin 1)).map f r) ≫ ·)
    ((Discrete.functor ((FiniteCube.coordinateCube (C := W → C) x (0 : Fin 1)).obj T)).map_id
      (Discrete.mk r))).trans (Category.comp_id _)

/-- Pull back the original color-indexed arrows without changing any component map. -/
def pullbackArrowFamily {X Xprime : W → C} (x : X ⟶ Xprime) (c : R → W) :
    (X ∘ c) ⟶ (Xprime ∘ c) :=
  fun r => x (c r)

private theorem familyMap_pullback_heq {X Xprime : W → C} (x : X ⟶ Xprime)
    (c : R → W) {S T : FiniteCube.Index 1} (h : S ⊆ T) (r : R) :
    HEq (FiniteCube.familyMap (fun _ : Fin 1 => pullbackArrowFamily x c) h (0 : Fin 1) r)
      (FiniteCube.familyMap (fun _ : Fin 1 => x) h (0 : Fin 1) (c r)) := by
  by_cases hS : (0 : Fin 1) ∈ S
  · have hT := h hS
    have hRS : FiniteCube.vertexFamily (fun _ : Fin 1 => X ∘ c)
        (fun _ => Xprime ∘ c) S 0 = Xprime ∘ c := ite_eq_left hS
    have hRT : FiniteCube.vertexFamily (fun _ : Fin 1 => X ∘ c)
        (fun _ => Xprime ∘ c) T 0 = Xprime ∘ c := ite_eq_left hT
    have hWS : FiniteCube.vertexFamily (fun _ : Fin 1 => X)
        (fun _ => Xprime) S 0 = Xprime := ite_eq_left hS
    have hWT : FiniteCube.vertexFamily (fun _ : Fin 1 => X)
        (fun _ => Xprime) T 0 = Xprime := ite_eq_left hT
    exact (pi_hom_heq_apply hRS hRT
      (FiniteCube.familyMap_selected (fun _ : Fin 1 => pullbackArrowFamily x c) h 0 hS) r).trans
        (pi_hom_heq_apply hWS hWT
          (FiniteCube.familyMap_selected (fun _ : Fin 1 => x) h 0 hS) (c r)).symm
  · by_cases hT : (0 : Fin 1) ∈ T
    · have hRS : FiniteCube.vertexFamily (fun _ : Fin 1 => X ∘ c)
          (fun _ => Xprime ∘ c) S 0 = X ∘ c := ite_eq_right hS
      have hRT : FiniteCube.vertexFamily (fun _ : Fin 1 => X ∘ c)
          (fun _ => Xprime ∘ c) T 0 = Xprime ∘ c := ite_eq_left hT
      have hWS : FiniteCube.vertexFamily (fun _ : Fin 1 => X)
          (fun _ => Xprime) S 0 = X := ite_eq_right hS
      have hWT : FiniteCube.vertexFamily (fun _ : Fin 1 => X)
          (fun _ => Xprime) T 0 = Xprime := ite_eq_left hT
      exact (pi_hom_heq_apply hRS hRT
        (FiniteCube.familyMap_added (fun _ : Fin 1 => pullbackArrowFamily x c) h 0 hS hT) r).trans
          (pi_hom_heq_apply hWS hWT
            (FiniteCube.familyMap_added (fun _ : Fin 1 => x) h 0 hS hT) (c r)).symm
    · have hRS : FiniteCube.vertexFamily (fun _ : Fin 1 => X ∘ c)
          (fun _ => Xprime ∘ c) S 0 = X ∘ c := ite_eq_right hS
      have hRT : FiniteCube.vertexFamily (fun _ : Fin 1 => X ∘ c)
          (fun _ => Xprime ∘ c) T 0 = X ∘ c := ite_eq_right hT
      have hWS : FiniteCube.vertexFamily (fun _ : Fin 1 => X)
          (fun _ => Xprime) S 0 = X := ite_eq_right hS
      have hWT : FiniteCube.vertexFamily (fun _ : Fin 1 => X)
          (fun _ => Xprime) T 0 = X := ite_eq_right hT
      exact (pi_hom_heq_apply hRS hRT
        (FiniteCube.familyMap_unselected (fun _ : Fin 1 => pullbackArrowFamily x c) h 0 hT) r).trans
          (pi_hom_heq_apply hWS hWT
            (FiniteCube.familyMap_unselected (fun _ : Fin 1 => x) h 0 hT) (c r)).symm

/-- Relabeling keeps the actual object of each original marked input. -/
theorem recolorCarrier_obj {X Xprime : W → C} (x : X ⟶ Xprime) (c : R → W)
    (M : MarkedColor R) :
    (markedInputCarrier (pullbackArrowFamily x c)).obj M =
      (recolorMarkedColor c ⋙ markedInputCarrier x).obj M := by
  change (if (0 : Fin 1) ∈ M.1 then Xprime ∘ c else X ∘ c) M.2.as =
    (if (0 : Fin 1) ∈ M.1 then Xprime else X) (c M.2.as)
  by_cases h : (0 : Fin 1) ∈ M.1 <;>
    simp only [h, ite_true, ite_false, Function.comp_apply]

/-- The two original marked carriers have the same actual original component object. -/
def recolorCarrierIso {X Xprime : W → C} (x : X ⟶ Xprime) (c : R → W) :
    markedInputCarrier (pullbackArrowFamily x c) ≅
      recolorMarkedColor c ⋙ markedInputCarrier x :=
  NatIso.ofComponents (fun M => eqToIso (recolorCarrier_obj x c M))
    (by
      rintro ⟨S, ⟨r⟩⟩ ⟨T, ⟨s⟩⟩ ⟨f, g⟩
      obtain rfl := Discrete.eq_of_hom g
      have hg : g = 𝟙 (Discrete.mk r) := Subsingleton.elim _ _
      cases hg
      let f' : S ⟶ T := f
      change (markedInputCarrier (pullbackArrowFamily x c)).map
          (show (S, Discrete.mk r) ⟶ (T, Discrete.mk r) from (f', 𝟙 _)) ≫ _ =
        _ ≫ (markedInputCarrier x).map
          (show (S, Discrete.mk (c r)) ⟶ (T, Discrete.mk (c r)) from (f', 𝟙 _))
      rw [markedCarrier_map_coordinate, markedCarrier_map_coordinate]
      change (FiniteCube.familyMap (fun _ : Fin 1 => pullbackArrowFamily x c)
          (leOfHom f') (0 : Fin 1) r) ≫ eqToHom (recolorCarrier_obj x c (T, Discrete.mk r)) =
        eqToHom (recolorCarrier_obj x c (S, Discrete.mk r)) ≫
          (FiniteCube.familyMap (fun _ : Fin 1 => x) (leOfHom f') (0 : Fin 1) (c r))
      apply eq_of_heq
      exact (comp_eqToHom_heq _ (recolorCarrier_obj x c (T, Discrete.mk r))).trans
        ((familyMap_pullback_heq x c (leOfHom f') r).trans
          (eqToHom_comp_heq _ (recolorCarrier_obj x c (S, Discrete.mk r))).symm))

variable [MonoidalCategory C] [SymmetricCategory C]

/-- The original symmetric tensor structure supplies the finite input tensors. -/
local instance recolorFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C

/-- Every original finite tensor and original leaf map survives the actual color relabelling. -/
def recolorInputTensorIso {X Xprime : W → C} (x : X ⟶ Xprime) (c : R → W) :
    inputTensorDiagram (pullbackArrowFamily x c) ≅
      recolorMarkedInputs c ⋙ inputTensorDiagram x :=
  Functor.isoWhiskerRight (FiniteFamily.mapIso (recolorCarrierIso x c)) FiniteTensor.tensor

end extension04_OrbitCells_Recolor
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells

section extension04_OrbitCells_InputCubeArrow
universe uc u v us

open CategoryTheory Limits MonoidalCategory Operad ProfileGeometry

attribute [local instance] FintypeCat.fintype

variable {W : Type uc} {C : Type u} [Category.{v} C]
  [HasColimitsOfSize.{us, us} C]

local instance inputArrowColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

/-- Every original proper input-set face maps to the actual full top vertex. -/
def inputSetTopCocone (P : ColoredProfile W) (F : ProfileInputSets P ⥤ C) :
    Cocone (originalPuncturedInclusion P ⋙ F) where
  pt := F.obj Finset.univ
  ι.app S := F.map (homOfLE (Finset.subset_univ S.1))
  ι.naturality S T f := by
    dsimp
    rw [← F.map_comp]
    exact (congrArg F.map (Subsingleton.elim _ _)).trans (Category.comp_id _).symm

/-- The actual original finite input-set cube induces its actual boundary Arrow. -/
def inputSetBoundaryArrow (P : ColoredProfile W) (F : ProfileInputSets P ⥤ C) : Arrow C :=
  Arrow.mk (colimit.desc _ (inputSetTopCocone P F))

/-- Every original proper face is retained in the actual induced Arrow. -/
@[reassoc]
theorem inputSetBoundaryArrow_face (P : ColoredProfile W) (F : ProfileInputSets P ⥤ C)
    (S : ProfilePuncturedInputSets P) :
    colimit.ι (originalPuncturedInclusion P ⋙ F) S ≫ (inputSetBoundaryArrow P F).hom =
      F.map (homOfLE (Finset.subset_univ S.1)) := colimit.ι_desc _ _

/-- The original cube iso induces the actual original proper-face colimit iso. -/
def inputSetBoundaryIso (P : ColoredProfile W) {F G : ProfileInputSets P ⥤ C}
    (e : F ≅ G) :
    colimit (originalPuncturedInclusion P ⋙ F) ≅ colimit (originalPuncturedInclusion P ⋙ G) :=
  (colim (J := ProfilePuncturedInputSets P) (C := C)).mapIso
    (Functor.isoWhiskerLeft (originalPuncturedInclusion P) e)

/-- The full boundary and top isomorphisms retain the original whole Arrow square. -/
theorem inputSetBoundaryIso_square (P : ColoredProfile W) {F G : ProfileInputSets P ⥤ C}
    (e : F ≅ G) :
    (inputSetBoundaryIso P e).hom ≫ (inputSetBoundaryArrow P G).hom =
      (inputSetBoundaryArrow P F).hom ≫ (e.app Finset.univ).hom := by
  apply colimit.hom_ext
  intro S
  let t := homOfLE (Finset.subset_univ S.1)
  have hL : colimit.ι (originalPuncturedInclusion P ⋙ F) S ≫
      ((inputSetBoundaryIso P e).hom ≫ (inputSetBoundaryArrow P G).hom) =
      (e.app S.1).hom ≫ G.map t :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (inputSetBoundaryArrow P G).hom)
        (ι_colimMap (Functor.whiskerLeft (originalPuncturedInclusion P) e.hom) S)).trans
        ((Category.assoc _ _ _).trans
          (congrArg ((e.app S.1).hom ≫ ·) (inputSetBoundaryArrow_face P G S))))
  have hR : colimit.ι (originalPuncturedInclusion P ⋙ F) S ≫
      ((inputSetBoundaryArrow P F).hom ≫ (e.app Finset.univ).hom) =
      F.map t ≫ (e.app Finset.univ).hom :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (e.app Finset.univ).hom) (inputSetBoundaryArrow_face P F S))
  exact hL.trans ((e.hom.naturality t).symm.trans hR.symm)

/-- The whole original cube iso gives the actual original boundary/top Arrow iso. -/
def inputSetBoundaryArrowIso (P : ColoredProfile W) {F G : ProfileInputSets P ⥤ C}
    (e : F ≅ G) : inputSetBoundaryArrow P F ≅ inputSetBoundaryArrow P G :=
  Arrow.isoMk (inputSetBoundaryIso P e) (e.app Finset.univ)
    (inputSetBoundaryIso_square P e)

end extension04_OrbitCells_InputCubeArrow
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells

section extension04_OrbitCells_RawRecolor
universe ur uw u v us

open CategoryTheory Limits MonoidalCategory Operad ProfileGeometry

attribute [local instance] FintypeCat.fintype

variable {R : Type ur} {W : Type uw} {C : Type u} [Category.{v} C]
  [HasColimitsOfSize.{us, us} C]

local instance rawRecolorColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

omit [HasColimitsOfSize.{us, us} C] in
/-- Compare the actual full input cubes through the original recolor functor equality. -/
def recoloredGeometryCubeIso (c : R → W) (d : W) (P : ColoredProfile R)
    (D : MarkedInputs W ⥤ C) :
    geometryInputTensorCube (recolorMarkedInputs c ⋙ D) P ≅
      geometryInputTensorCube D (recoloredProfile c d P) :=
  eqToIso (congrArg (fun F : ProfileInputSets P ⥤ MarkedInputs W => F ⋙ D)
    (recoloredInputCube c d P))

omit [HasColimitsOfSize.{us, us} C] in
/-- Each cube component keeps the actual original object at the unchanged subset. -/
theorem recoloredGeometryCubeIso_component (c : R → W) (d : W) (P : ColoredProfile R)
    (D : MarkedInputs W ⥤ C) (S : ProfileInputSets P) :
    (recoloredGeometryCubeIso c d P D).hom.app S =
      𝟙 ((geometryInputTensorCube (recolorMarkedInputs c ⋙ D) P).obj S) := by
  change (eqToHom (congrArg (fun F : ProfileInputSets P ⥤ MarkedInputs W => F ⋙ D)
    (recoloredInputCube c d P))).app S = _
  rw [eqToHom_app]
  exact eqToHom_refl ((geometryInputTensorCube (recolorMarkedInputs c ⋙ D) P).obj S) _

/-- Transport both original boundary and top maps by an explicit actual cube Arrow iso. -/
def recoloredGeometryArrowIso (c : R → W) (d : W) (P : ColoredProfile R)
    (D : MarkedInputs W ⥤ C) :
    Arrow.mk (geometryBoundaryToTop (recolorMarkedInputs c ⋙ D) P) ≅
      Arrow.mk (geometryBoundaryToTop D (recoloredProfile c d P)) :=
  inputSetBoundaryArrowIso P (recoloredGeometryCubeIso c d P D)

/-- Every proper face keeps its original quotient leg through the recolored boundary iso. -/
theorem recoloredGeometryArrowIso_face (c : R → W) (d : W) (P : ColoredProfile R)
    (D : MarkedInputs W ⥤ C) (S : ProfilePuncturedInputSets P) :
    colimit.ι (geometryPuncturedTensor (recolorMarkedInputs c ⋙ D) P) S ≫
        (recoloredGeometryArrowIso c d P D).hom.left =
      colimit.ι (geometryPuncturedTensor D (recoloredProfile c d P)) S := by
  have h := ι_colimMap
    (Functor.whiskerLeft (originalPuncturedInclusion P)
      (recoloredGeometryCubeIso c d P D).hom) S
  exact h.trans ((congrArg (· ≫ colimit.ι
    (geometryPuncturedTensor D (recoloredProfile c d P)) S)
    (recoloredGeometryCubeIso_component c d P D S.1)).trans (Category.id_comp _))

/-- The explicit boundary iso intertwines both actual original recolored group actions. -/
theorem recoloredGeometryArrowIso_aut (c : R → W) (hc : Function.Injective c)
    (d : W) (P : ColoredProfile R) (D : MarkedInputs W ⥤ C) (g : Aut P) :
    geometryAutMap (recolorMarkedInputs c ⋙ D) P g ≫
        (recoloredGeometryArrowIso c d P D).hom.left =
      (recoloredGeometryArrowIso c d P D).hom.left ≫
        geometryAutMap D (recoloredProfile c d P) ((recoloredProfileAutEquiv c hc d P) g) := by
  let F := recolorMarkedInputs c ⋙ D
  let Q := recoloredProfile c d P
  let gq := (recoloredProfileAutEquiv c hc d P) g
  apply colimit.hom_ext
  intro S
  let Sg := (profileAutPunctured P g).obj S
  have hm := congrArg D.map (recoloredAutVertex c hc d P g S.1)
  have hL : colimit.ι (geometryPuncturedTensor F P) S ≫
      (geometryAutMap F P g ≫ (recoloredGeometryArrowIso c d P D).hom.left) =
      F.map (profileAutInputVertexIso P g S.1).hom ≫
        colimit.ι (geometryPuncturedTensor D Q) Sg :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (recoloredGeometryArrowIso c d P D).hom.left)
        (geometryAutMap_face F P g S)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (F.map (profileAutInputVertexIso P g S.1).hom ≫ ·)
            (recoloredGeometryArrowIso_face c d P D Sg))))
  have hR : colimit.ι (geometryPuncturedTensor F P) S ≫
      ((recoloredGeometryArrowIso c d P D).hom.left ≫ geometryAutMap D Q gq) =
      D.map (profileAutInputVertexIso Q gq S.1).hom ≫
        colimit.ι (geometryPuncturedTensor D Q) Sg :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ geometryAutMap D Q gq)
        (recoloredGeometryArrowIso_face c d P D S)).trans
        (geometryAutMap_face D Q gq S))
  exact hL.trans ((congrArg (· ≫ colimit.ι (geometryPuncturedTensor D Q) Sg) hm).trans hR.symm)

/-- Both original recolored top actions pass through the same original top map. -/
theorem recoloredGeometryArrowIso_topAut (c : R → W) (hc : Function.Injective c)
    (d : W) (P : ColoredProfile R) (D : MarkedInputs W ⥤ C) (g : Aut P) :
    (geometryInputTopRepresentation (recolorMarkedInputs c ⋙ D) P g).asHom ≫
        (recoloredGeometryArrowIso c d P D).hom.right =
      (recoloredGeometryArrowIso c d P D).hom.right ≫
        (geometryInputTopRepresentation D (recoloredProfile c d P)
          ((recoloredProfileAutEquiv c hc d P) g)).asHom := by
  have h := congrArg D.map (recoloredTopAut c hc d P g)
  have hi := recoloredGeometryCubeIso_component c d P D Finset.univ
  change D.map ((recolorMarkedInputs c).map (originalInputTopHom P g).asIso.hom) ≫
      (recoloredGeometryCubeIso c d P D).hom.app Finset.univ =
    (recoloredGeometryCubeIso c d P D).hom.app Finset.univ ≫
      D.map (originalInputTopHom (recoloredProfile c d P)
        ((recoloredProfileAutEquiv c hc d P) g)).asIso.hom
  have hL : D.map ((recolorMarkedInputs c).map (originalInputTopHom P g).asIso.hom) ≫
      (recoloredGeometryCubeIso c d P D).hom.app Finset.univ =
      D.map ((recolorMarkedInputs c).map (originalInputTopHom P g).asIso.hom) :=
    (congrArg (D.map ((recolorMarkedInputs c).map (originalInputTopHom P g).asIso.hom) ≫ ·)
      hi).trans (Category.comp_id _)
  have hR : (recoloredGeometryCubeIso c d P D).hom.app Finset.univ ≫
      D.map (originalInputTopHom (recoloredProfile c d P)
        ((recoloredProfileAutEquiv c hc d P) g)).asIso.hom =
      D.map (originalInputTopHom (recoloredProfile c d P)
        ((recoloredProfileAutEquiv c hc d P) g)).asIso.hom :=
    (congrArg (· ≫ D.map (originalInputTopHom (recoloredProfile c d P)
      ((recoloredProfileAutEquiv c hc d P) g)).asIso.hom) hi).trans (Category.id_comp _)
  exact hL.trans (h.trans hR.symm)

/-- The explicit cube/colimit Arrow comparison is the full original action isomorphism. -/
def recoloredRawGeometryActionIso (c : R → W) (hc : Function.Injective c)
    (d : W) (P : ColoredProfile R) (D : MarkedInputs W ⥤ C) :
    rawGeometryArrowAction (recolorMarkedInputs c ⋙ D) P ≅
      (Action.res (Arrow C) (recoloredProfileAutEquiv c hc d P).toMonoidHom).obj
        (rawGeometryArrowAction D (recoloredProfile c d P)) :=
  Action.mkIso (recoloredGeometryArrowIso c d P D) (by
    intro g
    apply Arrow.hom_ext
    · exact recoloredGeometryArrowIso_aut c hc d P D g
    · exact recoloredGeometryArrowIso_topAut c hc d P D g)

end extension04_OrbitCells_RawRecolor
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells

section extension04_OrbitCells_SupportGroup
universe uc

open CategoryTheory Operad ProfileGeometry

attribute [local instance] FintypeCat.fintype

/-- The product group acts on the identical original expanded input tuple. -/
theorem multiplicityAutEquiv_symm_input {k : ℕ} (hk : 0 < k) (n : Fin k → ℕ)
    (g : MultiplicityGroup n) :
    ((multiplicityAutEquiv hk n).symm g).asIso.hom.inputEquiv =
      Equiv.sigmaCongrRight g := by
  apply Equiv.ext
  rintro ⟨r, i⟩
  rfl

variable {W : Type uc}

/-- The supported profile stays in the original palette with the original independent output. -/
theorem supported_recoloredProfile (P : ColoredProfile W) (hP : 0 < inputCount P) :
    recoloredProfile (supportedLabel P) P.outputColor
        (multiplicityProfile (supportCount_pos P hP) (supportedMultiplicity P)) =
      expandedProfile P := rfl

/-- Both original group identifications keep precisely the same expanded input permutation. -/
theorem supported_group_comparison (P : ColoredProfile W) (hP : 0 < inputCount P) :
    (recoloredProfileAutEquiv (supportedLabel P) (supportedLabel_injective P) P.outputColor
        (multiplicityProfile (supportCount_pos P hP) (supportedMultiplicity P))).toMonoidHom.comp
        (multiplicityAutEquiv (supportCount_pos P hP) (supportedMultiplicity P)).symm.toMonoidHom =
      (expandedProfileAutEquiv P).symm.toMonoidHom := by
  apply MonoidHom.ext
  intro g
  apply Aut.ext
  apply Iso.ext
  apply ColoredProfile.Hom.ext
  exact multiplicityAutEquiv_symm_input (supportCount_pos P hP) (supportedMultiplicity P) g

end extension04_OrbitCells_SupportGroup
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells

section extension04_OrbitCells_MatrixSupport
universe uc u v us

open CategoryTheory Limits MonoidalCategory Operad ProfileGeometry

attribute [local instance] FintypeCat.fintype

variable {W : Type uc} {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{us, us} C]

/-- Use the original symmetric tensor structure for the actual supported input action. -/
local instance supportActionFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance supportActionSmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J

/-- The literal family member is the same original arrow at its actual supported color. -/
def supportedArrows {X Xprime : W → C} (x : X ⟶ Xprime) (P : ColoredProfile W) :
    Fin (supportCount P) → Arrow C :=
  fun r => Arrow.mk (x (supportedLabel P r))

/-- Both finite-support raw actions keep all original subset and full-input maps. -/
def supportedRawProductActionIso {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (hP : 0 < inputCount P) :
    (Action.res (Arrow C)
        (multiplicityAutEquiv (supportCount_pos P hP)
          (supportedMultiplicity P)).symm.toMonoidHom).obj
        (rawProfileArrowAction (pullbackArrowFamily x (supportedLabel P))
          (multiplicityProfile (supportCount_pos P hP) (supportedMultiplicity P))) ≅
      (Action.res (Arrow C) (expandedProfileAutEquiv P).symm.toMonoidHom).obj
        (rawProfileArrowAction x (expandedProfile P)) := by
  let Q := multiplicityProfile (supportCount_pos P hP) (supportedMultiplicity P)
  let f := (multiplicityAutEquiv (supportCount_pos P hP) (supportedMultiplicity P)).symm.toMonoidHom
  let g := (recoloredProfileAutEquiv (supportedLabel P) (supportedLabel_injective P)
    P.outputColor Q).toMonoidHom
  let A := rawProfileArrowAction x (expandedProfile P)
  have er : rawProfileArrowAction (pullbackArrowFamily x (supportedLabel P)) Q ≅
      (Action.res (Arrow C) g).obj A :=
    rawGeometryActionIso (recolorInputTensorIso x (supportedLabel P)) Q ≪≫
      recoloredRawGeometryActionIso (supportedLabel P) (supportedLabel_injective P)
        P.outputColor Q (inputTensorDiagram x)
  exact (Action.res (Arrow C) f).mapIso er ≪≫
    (Action.resComp (Arrow C) f g).app A ≪≫
      (Action.resCongr (Arrow C) (supported_group_comparison P hP)).app A

/-- Transport the full supported raw Arrow comparison to both actual heterogeneous PP Arrows. -/
def supportedPushoutProductActionIso {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (hP : 0 < inputCount P) :
    matrixPushoutProductAction (supportCount_pos P hP) (supportedMultiplicity P)
        (supportedArrows x P) ≅
      (Action.res (Arrow C) (expandedProfileAutEquiv P).symm.toMonoidHom).obj
        (profilePushoutProductAction x (expandedProfile P)) := by
  let Q := multiplicityProfile (supportCount_pos P hP) (supportedMultiplicity P)
  let f := (multiplicityAutEquiv (supportCount_pos P hP) (supportedMultiplicity P)).symm.toMonoidHom
  let g := (expandedProfileAutEquiv P).symm.toMonoidHom
  have el := (Action.res (Arrow C) f).mapIso
    (Action.transportArrowActionIso (rawProfileArrowAction (pullbackArrowFamily x (supportedLabel P)) Q)
      (inputPushoutProductIso (pullbackArrowFamily x (supportedLabel P)) Q))
  have er := (Action.res (Arrow C) g).mapIso
    (Action.transportArrowActionIso (rawProfileArrowAction x (expandedProfile P))
      (inputPushoutProductIso x (expandedProfile P)))
  exact el.symm ≪≫ supportedRawProductActionIso x P hP ≪≫ er

end extension04_OrbitCells_MatrixSupport
end CategoryTheory.OperadicOrbitCells

namespace CategoryTheory.OperadicOrbitCells

section extension04_OrbitCells_ProfileFamilyOrbit
universe uc u v us

open CategoryTheory Limits MonoidalCategory Operad ProfileGeometry MorphismProperty

attribute [local instance] FintypeCat.fintype

variable {W : Type uc} {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{us, us} C]

/-- The original symmetric tensor structure supplies the literal supported family tensors. -/
local instance profileFamilyFiniteTensor : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance profileFamilySmallestColimits : HasColimitsOfSize.{0, 0} C where
  has_colimits_of_shape J := HasColimitsOfShape.of_essentiallySmall C J
local instance profileFamilyAutColimits (P : ColoredProfile W) :
    HasColimitsOfShape (SingleObj (Aut P)) C :=
  HasColimitsOfShape.of_essentiallySmall C _
local instance profileFamilyProductColimits {k : ℕ} (n : Fin k → ℕ) :
    HasColimitsOfShape (SingleObj (MultiplicityGroup n)) C :=
  HasColimitsOfShape.of_essentiallySmall C _

/-- Every original arbitrary coefficient is transported through the checked original group isos. -/
def supportedCoefficient (P : ColoredProfile W) (Y : Action C (Aut P)) :
    Action C (MultiplicityGroup (supportedMultiplicity P)) :=
  (Action.res C (expandedProfileAutEquiv P).symm.toMonoidHom).obj
    (profileCoefficientTransport (originalExpandedProfileIso P) Y)

/-- The original profile supplies its actual nonempty family and actual positive multiplicities. -/
def profilePositiveOrbitFamily {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (hP : 0 < inputCount P) (Y : Action C (Aut P)) :
    PositiveOrbitFamily C where
  colors := supportCount P
  colors_pos := supportCount_pos P hP
  multiplicity := supportedMultiplicity P
  multiplicity_pos := supportedMultiplicity_pos P
  arrows := supportedArrows x P
  coefficient := supportedCoefficient P Y

/-- The whole actual original profile PP orbit is the literal supported family orbit Arrow. -/
def profileFamilyOrbitIso {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (hP : 0 < inputCount P) (Y : Action C (Aut P)) :
    profileIteratedOrbitArrow x P Y ≅ familyOrbitArrow (profilePositiveOrbitFamily x P hP Y) := by
  let Yq := profileCoefficientTransport (originalExpandedProfileIso P) Y
  let A := profilePushoutProductAction x (expandedProfile P)
  let e := (expandedProfileAutEquiv P).symm
  have ep := coefficientOrbitActionIso (supportedCoefficient P Y)
    (supportedPushoutProductActionIso x P hP)
  have eg := coefficientOrbitGroupChangeIso e Yq (Action.actionUnderlyingHom A)
  exact profileIteratedOrbitReindexIso x (originalExpandedProfileIso P) Y ≪≫
    eg.symm ≪≫ ep.symm

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{us, us} C] in
/-- Membership of the original used arrows gives membership of every literal supported member. -/
theorem supportedArrows_mem (Q : MorphismProperty C) {X Xprime : W → C} (x : X ⟶ Xprime)
    (P : ColoredProfile W) (hx : ∀ i : P.inputs, Q (x (P.inputColor i)))
    (r : Fin (supportCount P)) : Q (supportedArrows x P r).hom := by
  obtain ⟨i, hi⟩ := (mem_profileColorSupport_iff P (supportedLabel P r)).1
    (supportEnumeration P r).2
  exact (congrArg (fun w : W => Q (x w)) hi).mp (hx i)

/-- Each positive original arbitrary-coefficient orbit belongs to the actual global source class. -/
theorem profileIteratedOrbitArrow_mem_isoClosure (Q : MorphismProperty C)
    {X Xprime : W → C} (x : X ⟶ Xprime) (P : ColoredProfile W) (hP : 0 < inputCount P)
    (Y : Action C (Aut P)) (hx : ∀ i : P.inputs, Q (x (P.inputColor i))) :
    (orbitGenerators Q).isoClosure (profileIteratedOrbitArrow x P Y).hom := by
  let s := profilePositiveOrbitFamily x P hP Y
  refine ⟨_, _, (familyOrbitArrow s).hom, familyOrbitArrow_mem Q s ?_,
    ⟨(profileFamilyOrbitIso x P hP Y).symm⟩⟩
  intro r
  exact supportedArrows_mem Q x P hx r

/-- The original input-set boundary orbit has the same complete positive source membership. -/
theorem profileOrbitArrow_mem_isoClosure (Q : MorphismProperty C)
    {X Xprime : W → C} (x : X ⟶ Xprime) (P : ColoredProfile W) (hP : 0 < inputCount P)
    (Y : Action C (Aut P)) (hx : ∀ i : P.inputs, Q (x (P.inputColor i))) :
    (orbitGenerators Q).isoClosure (profileOrbitArrow x P Y).hom :=
  ((orbitGenerators Q).isoClosure.arrow_iso_iff (profileOrbitPushoutProductIso x P Y)).2
    (profileIteratedOrbitArrow_mem_isoClosure Q x P hP Y hx)

end extension04_OrbitCells_ProfileFamilyOrbit
end CategoryTheory.OperadicOrbitCells
