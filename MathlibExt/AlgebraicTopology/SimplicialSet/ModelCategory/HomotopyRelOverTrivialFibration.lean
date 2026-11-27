/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyRelOver
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel
import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom
import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryOneMap

/-!
# Relative simplicial homotopies over a trivial fibration

Let p:E→B be a trivial simplicial fibration in universe u. If f₀,f₁:K→E agree on a subcomplex
A⊆K and satisfy f₀≫p=f₁≫p, there is a simplicial homotopy H:K⊗Δ[1]→E from f₀ to f₁, stationary
on A and lying over their common map to B.

The cylinder boundary and A⊗Δ[1] prescribe the homotopy on their union; trivial-fibration
lifting extends it to the full cylinder.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra
open MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite
open scoped Simplicial MonoidalCategory SSet.modelCategoryQuillen

universe u

namespace SSet

private theorem constIhom_uncurry (A B : SSet.{u}) (f : A ⟶ B) :
    MonoidalClosed.uncurry
        (SSet.const (X := (Δ[1] : SSet.{u})) (SSet.ihomVertexEquiv A B f)) =
      CartesianMonoidalCategory.fst A (Δ[1] : SSet.{u}) ≫ f := by
  apply MonoidalClosed.curry_injective
  rw [MonoidalClosed.curry_uncurry]
  apply (SSet.yonedaEquiv.{u}
    (X := (ihom A).obj B) (n := ⦋1⦌)).injective
  have h := congrArg (fun e : ((ihom A).obj B).Edge
      (SSet.ihomVertexEquiv A B f) (SSet.ihomVertexEquiv A B f) => e.edge)
    (SSet.Homotopy.edgeIhom_reflH f)
  rw [SSet.Homotopy.edgeIhom_edge, SSet.Homotopy.reflH_h, SSet.Edge.id_edge] at h
  have hConst : SSet.yonedaEquiv.{u}
      (X := (ihom A).obj B) (n := ⦋1⦌)
      (SSet.const (X := (Δ[1] : SSet.{u})) (SSet.ihomVertexEquiv A B f)) =
      ((ihom A).obj B).σ (0 : Fin 1) (SSet.ihomVertexEquiv A B f) := by
    change ((ihom A).obj B).map (⦋1⦌.const ⦋0⦌ 0).op _ = _
    have hMap : ⦋1⦌.const ⦋0⦌ 0 = SimplexCategory.σ (0 : Fin 1) := by
      ext i
      fin_cases i <;> rfl
    rw [hMap]
    rfl
  exact hConst.trans h.symm

/-- For K,E,B in simplicial-set universe u, let A⊆K be a subcomplex and p:E→B a trivial fibration.
Suppose f₀,f₁:K→E satisfy A.ι≫f₀=A.ι≫f₁ and f₀≫p=f₁≫p. Then there is H:K⊗Δ[1]→E with ι₀≫H=f₀,
ι₁≫H=f₁, H stationary on A, and H≫p=pr_K≫f₀≫p. This is a homotopy relative to A over B. -/
noncomputable def HomotopyRelOver.ofTrivialFibration {K E B : SSet.{u}} (S : K.Subcomplex)
    (p : E ⟶ B) (hp : trivialFibrations SSet.{u} p)
    (f₀ f₁ : K ⟶ E) (hS : S.ι ≫ f₀ = S.ι ≫ f₁) (hP : f₀ ≫ p = f₁ ≫ p) :
    HomotopyRelOver p f₀ f₁ S := by
  let _ : Cofibration S.ι := SSet.modelCategoryQuillen.cofibration_of_mono _
  let _ : Fibration p := (mem_trivialFibrations_iff p).mp hp |>.1
  let _ : WeakEquivalence p := (mem_trivialFibrations_iff p).mp hp |>.2
  let V : SSet.{u} := (ihom K).obj E
  let T : SSet.{u} := pullback ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B)
  let r : V ⟶ T := SSet.ihomToPullback S.ι p
  let v₀ : V.obj (op ⦋0⦌) := SSet.ihomVertexEquiv K E f₀
  let v₁ : V.obj (op ⦋0⦌) := SSet.ihomVertexEquiv K E f₁
  let b₀ : T.obj (op ⦋0⦌) := r.app (op ⦋0⦌) v₀
  have r_fst : r ≫ pullback.fst ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B) =
      (pre S.ι).app E := by
    change pullback.lift ((pre S.ι).app E) ((ihom K).map p)
        (MonoidalClosed.pre_comm_ihom_map S.ι p) ≫
        pullback.fst ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B) =
      (pre S.ι).app E
    exact pullback.lift_fst _ _ _
  have r_snd : r ≫ pullback.snd ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B) =
      (ihom K).map p := by
    change pullback.lift ((pre S.ι).app E) ((ihom K).map p)
        (MonoidalClosed.pre_comm_ihom_map S.ι p) ≫
        pullback.snd ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B) =
      (ihom K).map p
    exact pullback.lift_snd _ _ _
  have hFst₀ :
      (pullback.fst ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B)).app
          (op ⦋0⦌) (r.app (op ⦋0⦌) v₀) =
        SSet.ihomVertexEquiv (S : SSet.{u}) E (S.ι ≫ f₀) := by
    change (r ≫ pullback.fst ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B)).app
      (op ⦋0⦌) v₀ = _
    rw [r_fst]
    exact SSet.ihomVertexEquiv_pre_app S.ι f₀
  have hFst₁ :
      (pullback.fst ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B)).app
          (op ⦋0⦌) (r.app (op ⦋0⦌) v₁) =
        SSet.ihomVertexEquiv (S : SSet.{u}) E (S.ι ≫ f₁) := by
    change (r ≫ pullback.fst ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B)).app
      (op ⦋0⦌) v₁ = _
    rw [r_fst]
    exact SSet.ihomVertexEquiv_pre_app S.ι f₁
  have hSnd₀ :
      (pullback.snd ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B)).app
          (op ⦋0⦌) (r.app (op ⦋0⦌) v₀) =
        SSet.ihomVertexEquiv K B (f₀ ≫ p) := by
    change (r ≫ pullback.snd ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B)).app
      (op ⦋0⦌) v₀ = _
    rw [r_snd]
    exact SSet.ihomVertexEquiv_ihom_map f₀ p
  have hSnd₁ :
      (pullback.snd ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B)).app
          (op ⦋0⦌) (r.app (op ⦋0⦌) v₁) =
        SSet.ihomVertexEquiv K B (f₁ ≫ p) := by
    change (r ≫ pullback.snd ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B)).app
      (op ⦋0⦌) v₁ = _
    rw [r_snd]
    exact SSet.ihomVertexEquiv_ihom_map f₁ p
  have hSame : r.app (op ⦋0⦌) v₁ = b₀ := by
    change r.app (op ⦋0⦌) v₁ = r.app (op ⦋0⦌) v₀
    apply (SSet.yonedaEquiv.{u} (X := T) (n := ⦋0⦌)).symm.injective
    apply pullback.hom_ext
    · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp,
        hFst₁, hFst₀, hS]
    · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp,
        hSnd₁, hSnd₀, hP]
  have hr : trivialFibrations SSet.{u} r :=
    SSet.ihomToPullback_mem_trivialFibrations_of_right S.ι p
  let _ : Fibration r := (mem_trivialFibrations_iff r).mp hr |>.1
  let _ : WeakEquivalence r := (mem_trivialFibrations_iff r).mp hr |>.2
  let d : (∂Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) := (SSet.boundary 1).ι
  let _ : Cofibration d := SSet.modelCategoryQuillen.cofibration_of_mono _
  let a : (∂Δ[1] : SSet.{u}) ⟶ V := SSet.boundaryOneMap v₀ v₁
  let b : (Δ[1] : SSet.{u}) ⟶ T := SSet.const b₀
  let _ : HasLiftingProperty d r := ModelCategory.cm4b d r
  let sq : CommSq a d r b := by
    constructor
    apply SSet.boundary.hom_ext
    intro i
    fin_cases i
    · calc
        SSet.boundary.ι (0 : Fin 2) ≫ (a ≫ r) =
            (SSet.boundary.ι (0 : Fin 2) ≫ a) ≫ r :=
          (Category.assoc _ _ _).symm
        _ = (SSet.const (X := (Δ[0] : SSet.{u})) v₁) ≫ r :=
          congrArg (fun m : (Δ[0] : SSet.{u}) ⟶ V => m ≫ r)
            (SSet.boundary_ι_zero_boundaryOneMap v₀ v₁)
        _ = SSet.const (X := (Δ[0] : SSet.{u})) (r.app (op ⦋0⦌) v₁) :=
          SSet.const_comp (X := (Δ[0] : SSet.{u})) v₁ r
        _ = SSet.const (X := (Δ[0] : SSet.{u})) b₀ :=
          congrArg (fun v : T.obj (op ⦋0⦌) =>
            SSet.const (X := (Δ[0] : SSet.{u})) v) hSame
        _ = SSet.boundary.ι (0 : Fin 2) ≫ (d ≫ b) :=
          (SSet.comp_const (SSet.boundary.ι (0 : Fin 2) ≫ d) b₀).symm.trans
            (Category.assoc (SSet.boundary.ι (0 : Fin 2)) d b)
    · calc
        SSet.boundary.ι (1 : Fin 2) ≫ (a ≫ r) =
            (SSet.boundary.ι (1 : Fin 2) ≫ a) ≫ r :=
          (Category.assoc _ _ _).symm
        _ = (SSet.const (X := (Δ[0] : SSet.{u})) v₀) ≫ r :=
          congrArg (fun m : (Δ[0] : SSet.{u}) ⟶ V => m ≫ r)
            (SSet.boundary_ι_one_boundaryOneMap v₀ v₁)
        _ = SSet.const (X := (Δ[0] : SSet.{u})) b₀ :=
          SSet.const_comp (X := (Δ[0] : SSet.{u})) v₀ r
        _ = SSet.boundary.ι (1 : Fin 2) ≫ (d ≫ b) :=
          (SSet.comp_const (SSet.boundary.ι (1 : Fin 2) ≫ d) b₀).symm.trans
            (Category.assoc (SSet.boundary.ι (1 : Fin 2)) d b)
  let l : (Δ[1] : SSet.{u}) ⟶ V := sq.lift
  have h₀ : (SSet.stdSimplex.δ (1 : Fin 2) :
      (Δ[0] : SSet.{u}) ⟶ (Δ[1] : SSet.{u})) ≫ l =
      SSet.const (X := (Δ[0] : SSet.{u})) v₀ := by
    calc
      _ = (SSet.boundary.ι (1 : Fin 2) ≫ d) ≫ l := by
        change SSet.stdSimplex.δ (1 : Fin 2) ≫ l =
          (SSet.boundary.ι (1 : Fin 2) ≫ (SSet.boundary 1).ι) ≫ l
        rw [SSet.boundary.ι_ι]
      _ = SSet.boundary.ι (1 : Fin 2) ≫ a := by
        rw [Category.assoc, sq.fac_left]
      _ = SSet.const (X := (Δ[0] : SSet.{u})) v₀ :=
        SSet.boundary_ι_one_boundaryOneMap v₀ v₁
  have h₁ : (SSet.stdSimplex.δ (0 : Fin 2) :
      (Δ[0] : SSet.{u}) ⟶ (Δ[1] : SSet.{u})) ≫ l =
      SSet.const (X := (Δ[0] : SSet.{u})) v₁ := by
    calc
      _ = (SSet.boundary.ι (0 : Fin 2) ≫ d) ≫ l := by
        change SSet.stdSimplex.δ (0 : Fin 2) ≫ l =
          (SSet.boundary.ι (0 : Fin 2) ≫ (SSet.boundary 1).ι) ≫ l
        rw [SSet.boundary.ι_ι]
      _ = SSet.boundary.ι (0 : Fin 2) ≫ a := by
        rw [Category.assoc, sq.fac_left]
      _ = SSet.const (X := (Δ[0] : SSet.{u})) v₁ :=
        SSet.boundary_ι_zero_boundaryOneMap v₀ v₁
  let η : V.obj (op ⦋1⦌) :=
    SSet.yonedaEquiv.{u} (X := V) (n := ⦋1⦌) l
  have hη₀ : V.δ (1 : Fin 2) η = v₀ := by
    change V.δ (1 : Fin 2)
      (SSet.yonedaEquiv.{u} (X := V) (n := ⦋1⦌) l) = v₀
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp l (1 : Fin 2), h₀]
    exact SSet.yonedaEquiv_const v₀
  have hη₁ : V.δ (0 : Fin 2) η = v₁ := by
    change V.δ (0 : Fin 2)
      (SSet.yonedaEquiv.{u} (X := V) (n := ⦋1⦌) l) = v₁
    rw [← SSet.stdSimplex.yonedaEquiv_δ_comp l (0 : Fin 2), h₁]
    exact SSet.yonedaEquiv_const v₁
  let e : V.Edge v₀ v₁ := SSet.Edge.mk η hη₀ hη₁
  let H : SSet.Homotopy f₀ f₁ := SSet.Homotopy.ofIhomEdge e
  have hH : H.h = MonoidalClosed.uncurry l := by
    rw [SSet.Homotopy.ofIhomEdge_h]
    change MonoidalClosed.uncurry
        ((SSet.yonedaEquiv.{u} (X := V) (n := ⦋1⦌)).symm
          (SSet.yonedaEquiv.{u} (X := V) (n := ⦋1⦌) l)) =
      MonoidalClosed.uncurry l
    exact congrArg (fun m : (Δ[1] : SSet.{u}) ⟶ V => MonoidalClosed.uncurry m)
      ((SSet.yonedaEquiv.{u} (X := V) (n := ⦋1⦌)).symm_apply_apply l)
  have hPre : l ≫ (pre S.ι).app E =
      SSet.const (X := (Δ[1] : SSet.{u}))
        (SSet.ihomVertexEquiv (S : SSet.{u}) E (S.ι ≫ f₀)) := by
    calc
      _ = (l ≫ r) ≫ pullback.fst ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B) := by
        rw [Category.assoc, r_fst]
      _ = SSet.const b₀ ≫ pullback.fst ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B) :=
        congrArg (fun m : (Δ[1] : SSet.{u}) ⟶ T =>
          m ≫ pullback.fst ((ihom (S : SSet.{u})).map p)
            ((pre S.ι).app B)) sq.fac_right
      _ = _ := by rw [SSet.const_comp, hFst₀]
  have hPost : l ≫ (ihom K).map p =
      SSet.const (X := (Δ[1] : SSet.{u})) (SSet.ihomVertexEquiv K B (f₀ ≫ p)) := by
    calc
      _ = (l ≫ r) ≫ pullback.snd ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B) := by
        rw [Category.assoc, r_snd]
      _ = SSet.const b₀ ≫ pullback.snd ((ihom (S : SSet.{u})).map p) ((pre S.ι).app B) :=
        congrArg (fun m : (Δ[1] : SSet.{u}) ⟶ T =>
          m ≫ pullback.snd ((ihom (S : SSet.{u})).map p)
            ((pre S.ι).app B)) sq.fac_right
      _ = _ := by rw [SSet.const_comp, hSnd₀]
  have hStationary : (S.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.fst (S : SSet.{u}) (Δ[1] : SSet.{u}) ≫ S.ι ≫ f₀ := by
    rw [hH, ← MonoidalClosed.uncurry_pre_app, hPre, constIhom_uncurry]
  have hOver : H.h ≫ p =
      CartesianMonoidalCategory.fst K (Δ[1] : SSet.{u}) ≫ (f₀ ≫ p) := by
    rw [hH, ← MonoidalClosed.uncurry_natural_right, hPost, constIhom_uncurry]
  refine
    { toHomotopyRel := { h := H.h, h₀ := H.h₀, h₁ := H.h₁, stationary := ?_ }
      over := hOver }
  intro n x hx t
  exact congrArg
    (fun m : (S : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ E =>
      m.app n (⟨x, hx⟩, t)) hStationary

end SSet

end
