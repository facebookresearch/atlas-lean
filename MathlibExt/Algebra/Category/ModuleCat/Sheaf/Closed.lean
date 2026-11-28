/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @junekim623, Muse
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.Closed
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic

/-!
# Presheaf internal Hom and sheaf tensor products

Let `C : Type u` carry a category structure with morphisms in `Type u`, let `J` be a
Grothendieck topology, and let `R : Sheaf J CommRingCat.{u}`. The category of module
presheaves over `R.obj` is monoidal closed: each functor `M ↦ P ⊗_R M` has a right adjoint,
characterized by `Hom(P ⊗_R M,N) ≅ Hom(M,Hom_R(P,N))`.

Assume weak additive sheafification, the identification of sheafification equivalences with
locally bijective maps, monoidality of those equivalences, and preservation of the sheaf
condition by `CommRingCat → RingCat`. The tensor product of module sheaves is the
sheafification of the tensor product of their underlying module presheaves. These presheaf Hom
and sheaf tensor constructions give the setting for monoidal reflection.
-/
