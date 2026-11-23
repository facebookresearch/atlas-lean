/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathSpace
import MathlibExt.CategoryTheory.Monoidal.Closed.InternalHomInterchange

/-!
# The original interval-square coordinate interchange

The actual internal currying Iso is natural as a whole functor. It and
the existing symmetric braiding construct the complete double-internal-Hom
coordinate swap, with both original maps, all naturalities, involution and
the full twice-uncurried map. Specialization to the SAME simplicial path
space keeps its original constant-square points. The ambient symmetry is
that of the actual cartesian simplicial-set category. No symmetry of the
original reverse-power Sequential.Index is inferred.
-/

set_option autoImplicit false
noncomputable section
universe u v u₁ v₁
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped MonoidalClosed Simplicial


namespace SSet.OriginalLoopPathInterchangeGeometry

open CategoryTheory.MonoidalClosed.OriginalLoopInterchangeGeometry

/-- The whole original simplicial path functor is iterated on its SAME original carrier and maps. -/
def originalDoublePathFunctor : SSet.{u} ⥤ SSet.{u} :=
  ihom (Δ[1] : SSet.{u}) ⋙ ihom (Δ[1] : SSet.{u})

/-- The existing actual simplicial cartesian closure gives the entire original square-coordinate
Iso. -/
def originalDoublePathSwapNatIso : originalDoublePathFunctor.{u} ≅ originalDoublePathFunctor :=
  originalSelfInterchangeNatIso (Δ[1] : SSet.{u})

/-- Each SAME original simplicial double path space has both complete coordinate swap maps. -/
def originalDoublePathSwapIso (X : SSet.{u}) : pathSpace (pathSpace X) ≅ pathSpace (pathSpace X) :=
  originalDoublePathSwapNatIso.app X

/-- The entire original forward path swap has its complete original target-map naturality. -/
theorem originalDoublePathSwapIso_hom_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    originalDoublePathFunctor.map f ≫ (originalDoublePathSwapIso Y).hom =
      (originalDoublePathSwapIso X).hom ≫ originalDoublePathFunctor.map f :=
  originalDoublePathSwapNatIso.hom.naturality f

/-- The entire original inverse path swap has its complete original target-map naturality. -/
theorem originalDoublePathSwapIso_inv_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    originalDoublePathFunctor.map f ≫ (originalDoublePathSwapIso Y).inv =
      (originalDoublePathSwapIso X).inv ≫ originalDoublePathFunctor.map f :=
  originalDoublePathSwapNatIso.inv.naturality f

/-- Both complete original path coordinate maps agree as actual natural functions. -/
theorem originalDoublePathSwapNatIso_hom_eq_inv :
    originalDoublePathSwapNatIso.{u}.hom = originalDoublePathSwapNatIso.inv :=
  originalSelfInterchangeNatIso_hom_eq_inv (Δ[1] : SSet.{u})

/-- The full original path-coordinate map is an actual involution on the SAME original space. -/
theorem originalDoublePathSwapIso_involution (X : SSet.{u}) :
    (originalDoublePathSwapIso X).hom ≫ (originalDoublePathSwapIso X).hom =
      𝟙 (pathSpace (pathSpace X)) :=
  congrArg (fun t => t.app X) (originalSelfInterchangeNatIso_involution (Δ[1] : SSet.{u}))

/-- The original constant path inclusion is iterated as a whole actual natural transformation. -/
def originalDoubleConstPathNatTrans : 𝟭 SSet.{u} ⟶ originalDoublePathFunctor where
  app X := constPath X ≫ constPath (pathSpace X)
  naturality {X Y} f := by
    exact (Category.assoc f (constPath Y) (constPath (pathSpace Y))).symm.trans
      ((congrArg (fun h => h ≫ constPath (pathSpace Y)) (constPath_naturality f)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun h => constPath X ≫ h)
            (constPath_naturality ((ihom (Δ[1] : SSet.{u})).map f))).trans
              (Category.assoc _ _ _).symm)))

/-- The SAME original point simplex remains an actual terminal object after both original path
maps. -/
def originalDoublePointIsTerminal :
    IsTerminal (originalDoublePathFunctor.{u}.obj (Δ[0] : SSet.{u})) := by
  let := (ihom.adjunction (Δ[1] : SSet.{u})).rightAdjoint_preservesLimits
  exact IsTerminal.isTerminalObj (ihom (Δ[1] : SSet.{u}))
    (pathSpace (Δ[0] : SSet.{u}))
      (IsTerminal.isTerminalObj (ihom (Δ[1] : SSet.{u})) (Δ[0] : SSet.{u})
        stdSimplex.isTerminalObj₀)

/-- The full original swap on the SAME original double point is the actual identity map. -/
theorem originalDoublePathSwapIso_point_simplex :
    (originalDoublePathSwapIso (Δ[0] : SSet.{u})).hom = 𝟙 _ :=
  originalDoublePointIsTerminal.hom_ext _ _

/-- Every original selected vertex retains its SAME entire original constant-square point map. -/
theorem originalDoublePathSwapIso_constant_point_map (X : SSet.{u}) (x : X _⦋0⦌) :
    (SSet.const (X := Δ[0]) x ≫ originalDoubleConstPathNatTrans.app X) ≫
        (originalDoublePathSwapIso X).hom =
      SSet.const (X := Δ[0]) x ≫ originalDoubleConstPathNatTrans.app X := by
  let p : (Δ[0] : SSet.{u}) ⟶ X := SSet.const x
  let a := originalDoubleConstPathNatTrans.app (Δ[0] : SSet.{u})
  let f := originalDoublePathFunctor.map p
  let h := (originalDoublePathSwapIso X).hom
  let h₀ := (originalDoublePathSwapIso (Δ[0] : SSet.{u})).hom
  have hPoint : p ≫ originalDoubleConstPathNatTrans.app X = a ≫ f :=
    originalDoubleConstPathNatTrans.naturality p
  have hNatural : f ≫ h = h₀ ≫ f := originalDoublePathSwapNatIso.hom.naturality p
  have hTerminal : h₀ = 𝟙 _ := originalDoublePathSwapIso_point_simplex
  exact (congrArg (fun t => t ≫ h) hPoint).trans
    ((Category.assoc a f h).trans
      ((congrArg (fun t => a ≫ t) hNatural).trans
        ((congrArg (fun t => a ≫ (t ≫ f)) hTerminal).trans
          ((congrArg (fun t => a ≫ t) (Category.id_comp f)).trans hPoint.symm))))

end SSet.OriginalLoopPathInterchangeGeometry
