/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceMapOperator

/-!
# All actual endpoint-preserving simplicial necklace maps

Every full native simplicial necklace map retaining the same two
endpoints is the map of a unique original necklace morphism. The proof
uses its actual consecutive edges, all original simplex vertices, and
the same whole native standard-simplex readback.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

/-- The actual source-preserving full simplicial map retains its original zero operator. -/
theorem mapOperator_zero {T U : Data} (f : T.object.{u} ⟶ U.object.{u})
    (hf : T.source ≫ f = U.source) : (mapOperator f).toOrderHom 0 = 0 :=
  vertexMap_injective U ((vertexMap_map f 0).symm.trans hf)

/-- The actual target-preserving full simplicial map retains its original last operator. -/
theorem mapOperator_last {T U : Data} (f : T.object.{u} ⟶ U.object.{u})
    (hf : T.target ≫ f = U.target) :
    (mapOperator f).toOrderHom (Fin.last T.dimension) = Fin.last U.dimension :=
  vertexMap_injective U ((vertexMap_map f (Fin.last T.dimension)).symm.trans hf)

/-- The actual entire original map gives full native bead containment in the original small universe. -/
theorem mapOperator_lands {T U : Data} (f : T.object.{u} ⟶ U.object.{u}) :
    complex.{0} T.joints ≤
      (complex.{0} U.joints).preimage (SSet.stdSimplex.map (mapOperator f)) := by
  rintro ⟨⟨d⟩⟩ s₀ hs₀
  let s : (Δ[T.dimension] : SSet.{u}) _⦋d⦌ :=
    stdSimplex.objEquiv.{u}.symm (stdSimplex.objEquiv s₀)
  have hs : s ∈ (complex T.joints).obj (op ⦋d⦌) :=
    (mem_complex_iff T.joints s).mpr ((mem_complex_iff T.joints s₀).mp hs₀)
  let a : T.object _⦋d⦌ := ⟨s, hs⟩
  have hf : (f.app (op ⦋d⦌) a).val ∈ (complex U.joints).obj (op ⦋d⦌) :=
    (f.app (op ⦋d⦌) a).property
  have he := ConcreteCategory.congr_hom (congr_app (mapOperator_readback f) (op ⦋d⦌)) a
  have hm : (SSet.stdSimplex.map (mapOperator f)).app (op ⦋d⦌) s ∈
      (complex U.joints).obj (op ⦋d⦌) :=
    Eq.mp (congrArg (fun b : (Δ[U.dimension] : SSet.{u}) _⦋d⦌ =>
      b ∈ (complex U.joints).obj (op ⦋d⦌)) he) hf
  exact (mem_complex_iff U.joints
    ((SSet.stdSimplex.{0}.map (mapOperator f)).app (op ⦋d⦌) s₀)).mpr
      ((mem_complex_iff U.joints
        ((SSet.stdSimplex.{u}.map (mapOperator f)).app (op ⦋d⦌) s)).mp hm)

namespace Morphism

/-- The same actual endpoint-preserving full map as an original native necklace morphism. -/
def ofMap {T U : Data} (f : T.object.{u} ⟶ U.object.{u})
    (h₀ : T.source ≫ f = U.source) (h₁ : T.target ≫ f = U.target) :
    Morphism T U where
  operator := mapOperator f
  source := mapOperator_zero f h₀
  target := mapOperator_last f h₁
  lands := mapOperator_lands f

/-- The original native map is exactly the entire supplied simplicial map. -/
theorem ofMap_map {T U : Data} (f : T.object.{u} ⟶ U.object.{u})
    (h₀ : T.source ≫ f = U.source) (h₁ : T.target ≫ f = U.target) :
    (ofMap f h₀ h₁).map.{u} = f :=
  (cancel_mono (complex.{u} U.joints).ι).mp
    ((map_ι (ofMap f h₀ h₁)).trans (mapOperator_readback f).symm)

/-- The actual entire map retains its same original native necklace morphism in both directions. -/
theorem ofMap_original {T U : Data} (f : Morphism T U) :
    ofMap f.map.{u} (source_map f) (target_map f) = f :=
  map_injective (ofMap_map f.map (source_map f) (target_map f))

/-- Every actual full endpoint-preserving map has one same original native necklace morphism. -/
theorem existsUnique_map {T U : Data} (f : T.object.{u} ⟶ U.object.{u})
    (h₀ : T.source ≫ f = U.source) (h₁ : T.target ≫ f = U.target) :
    ∃! g : Morphism T U, g.map.{u} = f :=
  ⟨ofMap f h₀ h₁, ofMap_map f h₀ h₁, fun _g hg =>
    map_injective (hg.trans (ofMap_map f h₀ h₁).symm)⟩

/-- The entire original morphism type is equivalent to all actual bipointed native simplicial maps. -/
def pointedMapEquiv (T U : Data) :
    Morphism T U ≃ {f : T.object.{u} ⟶ U.object.{u} //
      T.source ≫ f = U.source ∧ T.target ≫ f = U.target} where
  toFun f := ⟨f.map, source_map f, target_map f⟩
  invFun f := ofMap f.val f.property.1 f.property.2
  left_inv := ofMap_original
  right_inv f := Subtype.ext (ofMap_map f.val f.property.1 f.property.2)

/-- The forward map is literally the same original whole simplicial map. -/
theorem pointedMapEquiv_apply (T U : Data) (f : Morphism T U) :
    (pointedMapEquiv.{u} T U f).val = f.map := rfl

end Morphism

end SSet.OriginalNecklace
