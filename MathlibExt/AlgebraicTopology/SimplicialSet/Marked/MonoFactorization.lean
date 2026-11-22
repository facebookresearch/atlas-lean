/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MonoLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# A genuine native marked mono weak factorization system

Reuse the actual simplicial mono small-object factorization. Equip its
original intermediate carrier with the literal preimage of the target
marking along its right factor. This gives a marked left monomorphism
and a marked right map lifting every marked monomorphism. The original
factorization equation and all simplices are retained. The resulting
weak factorization system concerns marked monomorphisms and their right
class; it asserts neither a marked weak-equivalence class nor straightening.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The actual original simplicial mono factorization with the literal target-preimage marking. -/
def monoFactorizationData {X Y : Marked.{u}} (f : X ⟶ Y) :
    MapFactorizationData (monomorphisms Marked.{u}) (monomorphisms Marked.{u}).rlp f := by
  let r := modelCategoryQuillen.monoFactorizationData f.hom
  let Z := comap Y r.p
  let i : X ⟶ Z := ⟨r.i, fun {e} he => by
    change r.p.app (op ⦋1⦌) (r.i.app (op ⦋1⦌) e) ∈ Y.marking
    have h := ConcreteCategory.congr_hom (congr_app r.fac (op ⦋1⦌)) e
    exact h.symm ▸ f.preserve he⟩
  let p : Z ⟶ Y := comapHom Y r.p
  refine ⟨Z, i, p, Hom.ext r.fac, ?_, ?_⟩
  · let _ : Mono i.hom := r.hi
    exact Hom.mono_of_underlying i
  · apply (monomorphisms_rlp_iff p).mpr
    exact ⟨r.hp, fun _ he => he⟩

/-- Every original marked map has the proved marked mono/right-lifting factorization. -/
theorem mono_hasFactorization :
    HasFactorization (monomorphisms Marked.{u}) (monomorphisms Marked.{u}).rlp :=
  ⟨fun f => ⟨monoFactorizationData f⟩⟩

/-- Marked monomorphisms and their native right class form a genuine weak factorization system. -/
theorem mono_isWeakFactorizationSystem :
    IsWeakFactorizationSystem (monomorphisms Marked.{u}) (monomorphisms Marked.{u}).rlp := by
  let _ : HasFactorization (monomorphisms Marked.{u}) (monomorphisms Marked.{u}).rlp :=
    mono_hasFactorization
  exact IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp => hp i hi)

/-- The chosen left factor preserves the complete original simplicial left factor. -/
@[simp]
theorem monoFactorizationData_i_hom {X Y : Marked.{u}} (f : X ⟶ Y) :
    (monoFactorizationData f).i.hom = (modelCategoryQuillen.monoFactorizationData f.hom).i := rfl

/-- The right factor retains the whole original simplicial right factor. -/
@[simp]
theorem monoFactorizationData_p_hom {X Y : Marked.{u}} (f : X ⟶ Y) :
    (monoFactorizationData f).p.hom = (modelCategoryQuillen.monoFactorizationData f.hom).p := rfl

/-- The intermediate marking is exactly the literal preimage of the supplied original target marking. -/
theorem monoFactorizationData_marking {X Y : Marked.{u}} (f : X ⟶ Y) :
    (monoFactorizationData f).Z.marking =
      (modelCategoryQuillen.monoFactorizationData f.hom).p.app (op ⦋1⦌) ⁻¹' Y.marking := rfl

end SSet.Marked
