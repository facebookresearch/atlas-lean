/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplexCoordinates
import MathlibExt.AlgebraicTopology.SimplicialSet.CoherentIso
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# Original full-J categorical cylinder data

The product is the actual chosen binary product.
The arbitrary vertex is transported by every original site map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.FreeGroupoidSimplex

/-- The constant map at the prescribed original target vertex. -/
def constantMap (n m : SimplexCategory) (w : Fin (m.len + 1)) :
    J.{u}.obj n ⟶ J.{u}.obj m := SSet.const (vertex.{u} m w)

/-- Every degree has the full constant original vertex tuple. -/
theorem constantMap_coordinates (n m : SimplexCategory) (w : Fin (m.len + 1))
    (d : ℕ) (x : (J.{u}.obj n).obj (op ⦋d⦌)) (i : Fin (d + 1)) :
    simplexVertexEquiv.{u} m d ((constantMap.{u} n m w).app (op ⦋d⦌) x) i = w := by
  change simplexVertexEquiv.{u} m d
    ((J.{u}.obj m).map (⦋d⦌.const ⦋0⦌ 0).op (vertex.{u} m w)) i = w
  rw [simplexVertexEquiv_operator.{u}, simplexVertexEquiv_vertex.{u}]

/-- Inverting those coordinates returns the same original constant simplex. -/
theorem constantMap_coordinates_inv (n m : SimplexCategory) (w : Fin (m.len + 1))
    (d : ℕ) (x : (J.{u}.obj n).obj (op ⦋d⦌)) :
    (simplexVertexEquiv.{u} m d).symm (fun _ => w) =
      (constantMap.{u} n m w).app (op ⦋d⦌) x := by
  apply (simplexVertexEquiv.{u} m d).injective
  funext i
  rw [Equiv.apply_symm_apply, constantMap_coordinates.{u}]

/-- The constant map retains every original simplicial operator. -/
theorem constantMap_operator (n m : SimplexCategory) (w : Fin (m.len + 1))
    {d e : ℕ} (g : ⦋d⦌ ⟶ ⦋e⦌) (x : (J.{u}.obj n).obj (op ⦋e⦌)) :
    (J.{u}.obj m).map g.op ((constantMap.{u} n m w).app (op ⦋e⦌) x) =
      (constantMap.{u} n m w).app (op ⦋d⦌) ((J.{u}.obj n).map g.op x) := by
  exact (congrArg (fun h => h x) ((constantMap.{u} n m w).naturality g.op)).symm

/-- Precomposing by the SAME arbitrary original site map leaves the target vertex fixed. -/
theorem constantMap_precomp {n m : SimplexCategory} (f : n ⟶ m)
    (p : SimplexCategory) (w : Fin (p.len + 1)) :
    J.{u}.map f ≫ constantMap.{u} m p w = constantMap.{u} n p w :=
  SSet.comp_const _ _

/-- Postcomposing carries the prescribed original vertex to f(v). -/
theorem constantMap_postcomp (p : SimplexCategory) {n m : SimplexCategory}
    (v : Fin (n.len + 1)) (f : n ⟶ m) :
    constantMap.{u} p n v ≫ J.{u}.map f = constantMap.{u} p m (f v) := by
  rw [constantMap, SSet.const_comp, J_map_vertex.{u}]
  rfl

/-- Both strict constant composites of the SAME reverse map, with no strict-Iso claim. -/
theorem map_inverse_constants {n m : SimplexCategory} (f : n ⟶ m)
    (v : Fin (n.len + 1)) :
    J.{u}.map f ≫ constantMap.{u} m n v = constantMap.{u} n n v ∧
      constantMap.{u} m n v ≫ J.{u}.map f = constantMap.{u} m m (f v) :=
  ⟨constantMap_precomp.{u} f n v, constantMap_postcomp.{u} m v f⟩

/-- The original E-cylinder selects x_i at true and the prescribed v at false. -/
def intervalContraction (n : SimplexCategory) (v : Fin (n.len + 1)) :
    (J.{u}.obj n ⨯ coherentIso.{u}) ⟶ J.{u}.obj n where
  app a := ↾fun z => (simplexVertexEquiv.{u} n a.unop.len).symm (fun i =>
    if coherentIso.vertexBool.{u}
        ((prod.snd : J.{u}.obj n ⨯ coherentIso.{u} ⟶ coherentIso.{u}).app a z) i then
      simplexVertexEquiv.{u} n a.unop.len
        ((prod.fst : J.{u}.obj n ⨯ coherentIso.{u} ⟶ J.{u}.obj n).app a z) i
    else v)
  naturality a b f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply (simplexVertexEquiv.{u} n b.unop.len).injective
    have hf := congrArg (fun h => h z)
      ((prod.fst : J.{u}.obj n ⨯ coherentIso.{u} ⟶ J.{u}.obj n).naturality f)
    have ht := congrArg (fun h => h z)
      ((prod.snd : J.{u}.obj n ⨯ coherentIso.{u} ⟶ coherentIso.{u}).naturality f)
    change
      (prod.fst : J.{u}.obj n ⨯ coherentIso.{u} ⟶ J.{u}.obj n).app b
        ((J.{u}.obj n ⨯ coherentIso.{u}).map f z) =
      (J.{u}.obj n).map f
        ((prod.fst : J.{u}.obj n ⨯ coherentIso.{u} ⟶ J.{u}.obj n).app a z) at hf
    change
      (prod.snd : J.{u}.obj n ⨯ coherentIso.{u} ⟶ coherentIso.{u}).app b
        ((J.{u}.obj n ⨯ coherentIso.{u}).map f z) =
      coherentIso.{u}.map f
        ((prod.snd : J.{u}.obj n ⨯ coherentIso.{u} ⟶ coherentIso.{u}).app a z) at ht
    funext i
    simp only [CategoryTheory.comp_apply]
    have ho := simplexVertexEquiv_operator.{u} n f.unop
      ((simplexVertexEquiv.{u} n a.unop.len).symm (fun j =>
        if coherentIso.vertexBool.{u}
            ((prod.snd : J.{u}.obj n ⨯ coherentIso.{u} ⟶ coherentIso.{u}).app a z) j then
          simplexVertexEquiv.{u} n a.unop.len
            ((prod.fst : J.{u}.obj n ⨯ coherentIso.{u} ⟶ J.{u}.obj n).app a z) j
        else v))
    have hp := simplexVertexEquiv_operator.{u} n f.unop
      ((prod.fst : J.{u}.obj n ⨯ coherentIso.{u} ⟶ J.{u}.obj n).app a z)
    rw [Quiver.Hom.op_unop] at ho hp
    simp only [TypeCat.ofHom_apply, Equiv.apply_symm_apply]
    rw [ho]
    rw [hf, ht, hp]
    rfl

/-- Both actual product projections occur in the full original output coordinates. -/
theorem intervalContraction_coordinates (n : SimplexCategory) (v : Fin (n.len + 1))
    (d : ℕ) (z : (J.{u}.obj n ⨯ coherentIso.{u}).obj (op ⦋d⦌)) (i : Fin (d + 1)) :
    simplexVertexEquiv.{u} n d ((intervalContraction.{u} n v).app (op ⦋d⦌) z) i =
      if coherentIso.vertexBool.{u}
          ((prod.snd : J.{u}.obj n ⨯ coherentIso.{u} ⟶ coherentIso.{u}).app (op ⦋d⦌) z) i then
        simplexVertexEquiv.{u} n d
          ((prod.fst : J.{u}.obj n ⨯ coherentIso.{u} ⟶ J.{u}.obj n).app (op ⦋d⦌) z) i
      else v := by
  exact congrFun ((simplexVertexEquiv.{u} n d).apply_symm_apply _) i

/-- Inverting the prescribed complete tuple gives the SAME cylinder value. -/
theorem intervalContraction_coordinates_inv (n : SimplexCategory)
    (v : Fin (n.len + 1)) (d : ℕ)
    (z : (J.{u}.obj n ⨯ coherentIso.{u}).obj (op ⦋d⦌)) :
    (simplexVertexEquiv.{u} n d).symm (fun i =>
      if coherentIso.vertexBool.{u}
          ((prod.snd : J.{u}.obj n ⨯ coherentIso.{u} ⟶ coherentIso.{u}).app (op ⦋d⦌) z) i then
        simplexVertexEquiv.{u} n d
          ((prod.fst : J.{u}.obj n ⨯ coherentIso.{u} ⟶ J.{u}.obj n).app (op ⦋d⦌) z) i
      else v) = (intervalContraction.{u} n v).app (op ⦋d⦌) z := rfl

/-- Every original simplicial operator is retained, not only faces or degeneracies. -/
theorem intervalContraction_operator (n : SimplexCategory) (v : Fin (n.len + 1))
    {d e : ℕ} (g : ⦋d⦌ ⟶ ⦋e⦌)
    (z : (J.{u}.obj n ⨯ coherentIso.{u}).obj (op ⦋e⦌)) :
    (J.{u}.obj n).map g.op ((intervalContraction.{u} n v).app (op ⦋e⦌) z) =
      (intervalContraction.{u} n v).app (op ⦋d⦌) ((J.{u}.obj n ⨯ coherentIso.{u}).map g.op z) :=
  (congrArg (fun h => h z) ((intervalContraction.{u} n v).naturality g.op)).symm

/-- Site naturality transports v to f(v), including maps moving zero or identifying vertices. -/
theorem intervalContraction_site {n m : SimplexCategory} (f : n ⟶ m)
    (v : Fin (n.len + 1)) :
    prod.map (J.{u}.map f) (𝟙 coherentIso.{u}) ≫ intervalContraction.{u} m (f v) =
      intervalContraction.{u} n v ≫ J.{u}.map f := by
  apply SSet.hom_ext
  intro a
  apply ConcreteCategory.hom_ext
  intro z
  apply (simplexVertexEquiv.{u} m a.unop.len).injective
  have hf := congrArg (fun h => h.app a z) (prod.map_fst (J.{u}.map f) (𝟙 coherentIso.{u}))
  have ht := congrArg (fun h => h.app a z) (prod.map_snd (J.{u}.map f) (𝟙 coherentIso.{u}))
  change
    (prod.fst : J.{u}.obj m ⨯ coherentIso.{u} ⟶ J.{u}.obj m).app a
      ((prod.map (J.{u}.map f) (𝟙 coherentIso.{u})).app a z) =
      (J.{u}.map f).app a ((prod.fst : J.{u}.obj n ⨯ coherentIso.{u} ⟶ J.{u}.obj n).app a z) at hf
  change
    (prod.snd : J.{u}.obj m ⨯ coherentIso.{u} ⟶ coherentIso.{u}).app a
      ((prod.map (J.{u}.map f) (𝟙 coherentIso.{u})).app a z) =
      (prod.snd : J.{u}.obj n ⨯ coherentIso.{u} ⟶ coherentIso.{u}).app a z at ht
  funext i
  change
    simplexVertexEquiv.{u} m a.unop.len
      ((intervalContraction.{u} m (f v)).app a
        ((prod.map (J.{u}.map f) (𝟙 coherentIso.{u})).app a z)) i =
      simplexVertexEquiv.{u} m a.unop.len
        ((J.{u}.map f).app a ((intervalContraction.{u} n v).app a z)) i
  rw [intervalContraction_coordinates.{u}, hf, ht, simplexVertexEquiv_site.{u},
    simplexVertexEquiv_site.{u}]
  dsimp only
  rw [intervalContraction_coordinates.{u}]
  cases coherentIso.vertexBool.{u}
    ((prod.snd : J.{u}.obj n ⨯ coherentIso.{u} ⟶ coherentIso.{u}).app a z) i <;> rfl

/-- False is the original E-zero endpoint; Delta0 is kept as its actual object. -/
theorem intervalContraction_zero (n : SimplexCategory) (v : Fin (n.len + 1)) :
    prod.map (𝟙 (J.{u}.obj n)) (SSet.yonedaEquiv.symm coherentIso.x₀.{u}) ≫
        intervalContraction.{u} n v =
      (prod.fst : J.{u}.obj n ⨯ (Δ[0] : SSet.{u}) ⟶ J.{u}.obj n) ≫ constantMap.{u} n n v := by
  apply SSet.hom_ext
  intro a
  apply ConcreteCategory.hom_ext
  intro z
  apply (simplexVertexEquiv.{u} n a.unop.len).injective
  have ht := congrArg (fun h => h.app a z)
    (prod.map_snd (𝟙 (J.{u}.obj n)) (SSet.yonedaEquiv.symm coherentIso.x₀.{u}))
  change (prod.snd : J.{u}.obj n ⨯ coherentIso.{u} ⟶ coherentIso.{u}).app a
      ((prod.map (𝟙 (J.{u}.obj n)) (SSet.yonedaEquiv.symm coherentIso.x₀.{u})).app a z) =
    (SSet.yonedaEquiv.symm coherentIso.x₀.{u}).app a
      ((prod.snd : J.{u}.obj n ⨯ (Δ[0] : SSet.{u}) ⟶ Δ[0]).app a z) at ht
  funext i
  change simplexVertexEquiv.{u} n a.unop.len
    ((intervalContraction.{u} n v).app a
      ((prod.map (𝟙 _) (SSet.yonedaEquiv.symm coherentIso.x₀.{u})).app a z)) i =
    simplexVertexEquiv.{u} n a.unop.len
      ((constantMap.{u} n n v).app a
        ((prod.fst : J.{u}.obj n ⨯ (Δ[0] : SSet.{u}) ⟶ J.{u}.obj n).app a z)) i
  rw [intervalContraction_coordinates.{u}, ht, constantMap_coordinates.{u}]
  have hzero : coherentIso.vertexBool.{u}
      ((SSet.yonedaEquiv.symm coherentIso.x₀.{u}).app a
        ((prod.snd : J.{u}.obj n ⨯ (Δ[0] : SSet.{u}) ⟶ Δ[0]).app a z)) i = false := by
    rw [SSet.yonedaEquiv_symm_app]
    rfl
  rw [hzero]
  rfl

/-- True is the original E-one endpoint, with the SAME original Cartesian first projection. -/
theorem intervalContraction_one (n : SimplexCategory) (v : Fin (n.len + 1)) :
    prod.map (𝟙 (J.{u}.obj n)) (SSet.yonedaEquiv.symm coherentIso.x₁.{u}) ≫
        intervalContraction.{u} n v =
      (prod.fst : J.{u}.obj n ⨯ (Δ[0] : SSet.{u}) ⟶ J.{u}.obj n) := by
  apply SSet.hom_ext
  intro a
  apply ConcreteCategory.hom_ext
  intro z
  apply (simplexVertexEquiv.{u} n a.unop.len).injective
  have hf := congrArg (fun h => h.app a z)
    (prod.map_fst (𝟙 (J.{u}.obj n)) (SSet.yonedaEquiv.symm coherentIso.x₁.{u}))
  have ht := congrArg (fun h => h.app a z)
    (prod.map_snd (𝟙 (J.{u}.obj n)) (SSet.yonedaEquiv.symm coherentIso.x₁.{u}))
  change (prod.fst : J.{u}.obj n ⨯ coherentIso.{u} ⟶ J.{u}.obj n).app a
      ((prod.map (𝟙 (J.{u}.obj n)) (SSet.yonedaEquiv.symm coherentIso.x₁.{u})).app a z) =
    (prod.fst : J.{u}.obj n ⨯ (Δ[0] : SSet.{u}) ⟶ J.{u}.obj n).app a z at hf
  change (prod.snd : J.{u}.obj n ⨯ coherentIso.{u} ⟶ coherentIso.{u}).app a
      ((prod.map (𝟙 (J.{u}.obj n)) (SSet.yonedaEquiv.symm coherentIso.x₁.{u})).app a z) =
    (SSet.yonedaEquiv.symm coherentIso.x₁.{u}).app a
      ((prod.snd : J.{u}.obj n ⨯ (Δ[0] : SSet.{u}) ⟶ Δ[0]).app a z) at ht
  funext i
  change simplexVertexEquiv.{u} n a.unop.len
    ((intervalContraction.{u} n v).app a
      ((prod.map (𝟙 _) (SSet.yonedaEquiv.symm coherentIso.x₁.{u})).app a z)) i = _
  rw [intervalContraction_coordinates.{u}, hf, ht]
  have hone : coherentIso.vertexBool.{u}
      ((SSet.yonedaEquiv.symm coherentIso.x₁.{u}).app a
        ((prod.snd : J.{u}.obj n ⨯ (Δ[0] : SSet.{u}) ⟶ Δ[0]).app a z)) i = true := by
    rw [SSet.yonedaEquiv_symm_app]
    rfl
  rw [hone]
  rfl

/-- The actual full-J1-to-E map, given on every original vertex tuple. -/
def coherentIntervalHom : J.{u}.obj ⦋1⦌ ⟶ coherentIso.{u} where
  app a := ↾fun x =>
    { obj := fun i => WalkingIso.equivBool.{u}.symm
        (decide (simplexVertexEquiv.{u} ⦋1⦌ a.unop.len x i = (1 : Fin 2)))
      map := fun _ => default
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ => Subsingleton.elim _ _ }
  naturality a b f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply coherentIso.eq_of_forall_vertexBool_eq.{u}
    intro i
    change
      WalkingIso.equivBool.{u} (WalkingIso.equivBool.{u}.symm
        (decide (simplexVertexEquiv.{u} ⦋1⦌ b.unop.len ((J.{u}.obj ⦋1⦌).map f x) i = 1))) =
      WalkingIso.equivBool.{u} (WalkingIso.equivBool.{u}.symm
        (decide (simplexVertexEquiv.{u} ⦋1⦌ a.unop.len x (f.unop i) = 1)))
    have h := congrFun (simplexVertexEquiv_operator.{u} ⦋1⦌ f.unop x) i
    rw [Quiver.Hom.op_unop] at h
    rw [h]

/-- The actual E-to-full-J1 map; false/true give original vertices zero/one. -/
def coherentIntervalInv : coherentIso.{u} ⟶ J.{u}.obj ⦋1⦌ where
  app a := ↾fun t => (simplexVertexEquiv.{u} ⦋1⦌ a.unop.len).symm (fun i =>
    if coherentIso.vertexBool.{u} t i then (1 : Fin 2) else 0)
  naturality a b f := by
    apply ConcreteCategory.hom_ext
    intro t
    apply (simplexVertexEquiv.{u} ⦋1⦌ b.unop.len).injective
    funext i
    rfl

/-- The original hom coordinates carry Fin2 to Bool with zero=false and one=true. -/
theorem coherentIntervalHom_coordinates (d : ℕ)
    (x : (J.{u}.obj ⦋1⦌).obj (op ⦋d⦌)) (i : Fin (d + 1)) :
    coherentIso.vertexBool.{u} (coherentIntervalHom.{u}.app (op ⦋d⦌) x) i =
      decide (simplexVertexEquiv.{u} ⦋1⦌ d x i = (1 : Fin 2)) := by
  exact WalkingIso.equivBool.{u}.apply_symm_apply _

/-- The original inverse coordinates carry Bool to the SAME Fin2 vertex tuple. -/
theorem coherentIntervalInv_coordinates (d : ℕ)
    (t : coherentIso.{u}.obj (op ⦋d⦌)) (i : Fin (d + 1)) :
    simplexVertexEquiv.{u} ⦋1⦌ d (coherentIntervalInv.{u}.app (op ⦋d⦌) t) i =
      if coherentIso.vertexBool.{u} t i then (1 : Fin 2) else 0 := by
  exact congrFun ((simplexVertexEquiv.{u} ⦋1⦌ d).apply_symm_apply _) i

/-- Every original simplicial operator is respected by the full hom map. -/
theorem coherentIntervalHom_operator {d e : ℕ} (g : ⦋d⦌ ⟶ ⦋e⦌)
    (x : (J.{u}.obj ⦋1⦌).obj (op ⦋e⦌)) :
    coherentIso.{u}.map g.op (coherentIntervalHom.{u}.app (op ⦋e⦌) x) =
      coherentIntervalHom.{u}.app (op ⦋d⦌) ((J.{u}.obj ⦋1⦌).map g.op x) :=
  (congrArg (fun h => h x) (coherentIntervalHom.{u}.naturality g.op)).symm

/-- Every original simplicial operator is respected by the SAME full inverse map. -/
theorem coherentIntervalInv_operator {d e : ℕ} (g : ⦋d⦌ ⟶ ⦋e⦌)
    (t : coherentIso.{u}.obj (op ⦋e⦌)) :
    (J.{u}.obj ⦋1⦌).map g.op (coherentIntervalInv.{u}.app (op ⦋e⦌) t) =
      coherentIntervalInv.{u}.app (op ⦋d⦌) (coherentIso.{u}.map g.op t) :=
  (congrArg (fun h => h t) (coherentIntervalInv.{u}.naturality g.op)).symm

/-- The actual full simplicial-set Iso, not a definitional equality J1=E. -/
def coherentIntervalIso : J.{u}.obj ⦋1⦌ ≅ coherentIso.{u} where
  hom := coherentIntervalHom.{u}
  inv := coherentIntervalInv.{u}
  hom_inv_id := by
    apply SSet.hom_ext
    intro a
    apply ConcreteCategory.hom_ext
    intro x
    apply (simplexVertexEquiv.{u} ⦋1⦌ a.unop.len).injective
    funext i
    change simplexVertexEquiv.{u} ⦋1⦌ a.unop.len
      (coherentIntervalInv.{u}.app a (coherentIntervalHom.{u}.app a x)) i =
        simplexVertexEquiv.{u} ⦋1⦌ a.unop.len x i
    rw [coherentIntervalInv_coordinates.{u}, coherentIntervalHom_coordinates.{u}]
    refine Fin.cases ?_ (fun j => ?_) (simplexVertexEquiv.{u} ⦋1⦌ a.unop.len x i)
    · rfl
    · have h : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro a
    apply ConcreteCategory.hom_ext
    intro t
    apply coherentIso.eq_of_forall_vertexBool_eq.{u}
    intro i
    change coherentIso.vertexBool.{u}
      (coherentIntervalHom.{u}.app a (coherentIntervalInv.{u}.app a t)) i =
        coherentIso.vertexBool.{u} t i
    rw [coherentIntervalHom_coordinates.{u}, coherentIntervalInv_coordinates.{u}]
    cases coherentIso.vertexBool.{u} t i <;> rfl

/-- The Iso hom is the displayed original all-degree hom map. -/
theorem coherentIntervalIso_hom : coherentIntervalIso.{u}.hom = coherentIntervalHom.{u} := rfl

/-- The Iso inverse is the displayed original all-degree inverse map. -/
theorem coherentIntervalIso_inv : coherentIntervalIso.{u}.inv = coherentIntervalInv.{u} := rfl

/-- Both ORIGINAL J1 vertices are carried to their ORIGINAL E endpoints. -/
theorem coherentIntervalHom_vertices :
    coherentIntervalHom.{u}.app (op ⦋0⦌) (vertex.{u} ⦋1⦌ 0) = coherentIso.x₀.{u} ∧
      coherentIntervalHom.{u}.app (op ⦋0⦌) (vertex.{u} ⦋1⦌ 1) = coherentIso.x₁.{u} := by
  constructor
  · apply coherentIso.eq_of_forall_vertexBool_eq.{u}
    intro i
    rw [coherentIntervalHom_coordinates.{u}, simplexVertexEquiv_vertex.{u}]
    rfl
  · apply coherentIso.eq_of_forall_vertexBool_eq.{u}
    intro i
    rw [coherentIntervalHom_coordinates.{u}, simplexVertexEquiv_vertex.{u}]
    rfl

/-- Both ORIGINAL E endpoints are recovered by the SAME inverse map. -/
theorem coherentIntervalInv_vertices :
    coherentIntervalInv.{u}.app (op ⦋0⦌) coherentIso.x₀.{u} = vertex.{u} ⦋1⦌ 0 ∧
      coherentIntervalInv.{u}.app (op ⦋0⦌) coherentIso.x₁.{u} = vertex.{u} ⦋1⦌ 1 := by
  constructor
  · apply (simplexVertexEquiv.{u} ⦋1⦌ 0).injective
    funext i
    rw [coherentIntervalInv_coordinates.{u}, simplexVertexEquiv_vertex.{u}]
    rfl
  · apply (simplexVertexEquiv.{u} ⦋1⦌ 0).injective
    funext i
    rw [coherentIntervalInv_coordinates.{u}, simplexVertexEquiv_vertex.{u}]
    rfl

/-- Both hom and inverse preserve the literal original Delta0 endpoint maps. -/
theorem coherentIntervalIso_endpoints :
    SSet.yonedaEquiv.symm (vertex.{u} ⦋1⦌ 0) ≫ coherentIntervalIso.{u}.hom =
        SSet.yonedaEquiv.symm coherentIso.x₀.{u} ∧
      SSet.yonedaEquiv.symm (vertex.{u} ⦋1⦌ 1) ≫ coherentIntervalIso.{u}.hom =
        SSet.yonedaEquiv.symm coherentIso.x₁.{u} ∧
      SSet.yonedaEquiv.symm coherentIso.x₀.{u} ≫ coherentIntervalIso.{u}.inv =
        SSet.yonedaEquiv.symm (vertex.{u} ⦋1⦌ 0) ∧
      SSet.yonedaEquiv.symm coherentIso.x₁.{u} ≫ coherentIntervalIso.{u}.inv =
        SSet.yonedaEquiv.symm (vertex.{u} ⦋1⦌ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply SSet.yonedaEquiv.injective
  · simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, coherentIntervalIso_hom.{u}]
      using coherentIntervalHom_vertices.{u}.1
  · simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, coherentIntervalIso_hom.{u}]
      using coherentIntervalHom_vertices.{u}.2
  · simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, coherentIntervalIso_inv.{u}]
      using coherentIntervalInv_vertices.{u}.1
  · simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, coherentIntervalIso_inv.{u}]
      using coherentIntervalInv_vertices.{u}.2

end SSet.FreeGroupoidSimplex
