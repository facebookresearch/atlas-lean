/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Interval
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Monomorphisms
import Mathlib.CategoryTheory.Generator.StrongGenerator
import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.CategoryTheory.Types.Basic

/-!
# A small strong generator of the original marked carrier

The minimally marked standard simplices detect every original simplex.
The maximally marked interval additionally detects the original marking.
Together they form a small strong generator at every original value universe.
The interval condition is essential: an underlying isomorphism alone need
not be an isomorphism of the supplied markings.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original simplices and the marked-edge classifier, without universe lowering. -/
def strongGeneratorObj : Option ℕ → Marked.{u}
  | some n => min (Δ[n] : SSet.{u})
  | none => max (Δ[1] : SSet.{u})

/-- The actual image property of these original marked objects. -/
def strongGenerator : ObjectProperty Marked.{u} := ObjectProperty.ofObj strongGeneratorObj

/-- The generator family is small in every original working universe. -/
theorem strongGenerator_small : ObjectProperty.Small.{u} strongGenerator.{u} := by
  change ObjectProperty.Small.{u} (ObjectProperty.ofObj strongGeneratorObj.{u})
  infer_instance

/-- A minimally marked standard simplex belongs to the actual generator. -/
theorem strongGenerator_min (n : ℕ) : strongGenerator.{u} (min (Δ[n] : SSet.{u})) :=
  ObjectProperty.ofObj.mk (some n)

/-- The fully marked original interval belongs to the actual generator. -/
theorem strongGenerator_interval : strongGenerator.{u} (max (Δ[1] : SSet.{u})) :=
  ObjectProperty.ofObj.mk none

/-- Testing the original minimally marked simplices separates all marked maps. -/
theorem strongGenerator_isSeparating : strongGenerator.{u}.IsSeparating := by
  intro X Y f g h
  apply Hom.ext
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro a
  let q : min (SSet.stdSimplex.obj n.unop) ⟶ X := ofMin (SSet.yonedaEquiv.symm a)
  have he := congrArg Hom.hom (h _ (strongGenerator_min n.unop.len) q)
  change SSet.yonedaEquiv.symm a ≫ f.hom = SSet.yonedaEquiv.symm a ≫ g.hom at he
  have hy := congrArg SSet.yonedaEquiv he
  simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hy

/-- Generator-surjectivity gives surjectivity on every original simplex. -/
theorem surjective_app_of_strongGenerator {X Y : Marked.{u}} (i : X ⟶ Y)
    (hi : ∀ G (_ : strongGenerator G), Function.Surjective (fun (f : G ⟶ X) => f ≫ i))
    (n : SimplexCategory) : Function.Surjective (i.hom.app (op n)) := by
  intro a
  let q : min (SSet.stdSimplex.obj n) ⟶ Y := ofMin (SSet.yonedaEquiv.symm a)
  obtain ⟨f, hf⟩ := hi _ (strongGenerator_min n.len) q
  refine ⟨SSet.yonedaEquiv f.hom, ?_⟩
  have hy := congrArg SSet.yonedaEquiv (congrArg Hom.hom hf)
  change SSet.yonedaEquiv (f.hom ≫ i.hom) = SSet.yonedaEquiv (SSet.yonedaEquiv.symm a) at hy
  rw [← Equiv.symm_apply_apply SSet.yonedaEquiv f.hom] at hy
  simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hy

/-- The original marked interval makes a monic generator-surjective map reflect markings. -/
theorem marking_reflection_of_strongGenerator {X Y : Marked.{u}} (i : X ⟶ Y) [Mono i]
    (hi : ∀ G (_ : strongGenerator G), Function.Surjective (fun (f : G ⟶ X) => f ≫ i))
    (e : X.toSSet _⦋1⦌) (he : i.hom.app (op ⦋1⦌) e ∈ Y.marking) : e ∈ X.marking := by
  obtain ⟨f, hf⟩ := hi _ strongGenerator_interval
    (intervalMapOfMarkedEdge (i.hom.app (op ⦋1⦌) e) he)
  have hy := congrArg SSet.yonedaEquiv (congrArg Hom.hom hf)
  change SSet.yonedaEquiv (f.hom ≫ i.hom) =
    SSet.yonedaEquiv (SSet.yonedaEquiv.symm (i.hom.app (op ⦋1⦌) e)) at hy
  rw [← Equiv.symm_apply_apply SSet.yonedaEquiv f.hom] at hy
  have heq : SSet.yonedaEquiv f.hom = e := (i.injective_app ⦋1⦌) (by
    simpa only [SSet.yonedaEquiv_comp, intervalMapOfMarkedEdge_hom,
      Equiv.apply_symm_apply] using hy)
  exact heq ▸ f.preserve (Set.mem_univ _)

/-- These two types of original tests detect the full marked isomorphism, not only its carrier. -/
theorem isIso_of_strongGenerator {X Y : Marked.{u}} (i : X ⟶ Y) [Mono i]
    (hi : ∀ G (_ : strongGenerator G), Function.Surjective (fun (f : G ⟶ X) => f ≫ i)) :
    IsIso i := by
  let _ : ∀ n : SimplexCategoryᵒᵖ, IsIso (i.hom.app n) := fun n =>
    (CategoryTheory.isIso_iff_bijective _).mpr
      ⟨i.injective_app n.unop, surjective_app_of_strongGenerator i hi n.unop⟩
  let _ : IsIso i.hom := NatIso.isIso_of_isIso_app i.hom
  let e : X ≅ Y := isoMk (asIso i.hom) (fun a =>
    ⟨i.preserve, marking_reflection_of_strongGenerator i hi a⟩)
  have h : e.hom = i := Hom.ext rfl
  exact h ▸ e.isIso_hom

/-- The native marked carrier has a small strong generator detecting simplices and actual marks. -/
theorem strongGenerator_isStrongGenerator : strongGenerator.{u}.IsStrongGenerator :=
  ObjectProperty.isStrongGenerator_iff.mpr
    ⟨strongGenerator_isSeparating, fun _ _ i _ hi => isIso_of_strongGenerator i hi⟩

end SSet.Marked
