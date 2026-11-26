/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGeometricPointsCommonUniverse
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGammaPullback
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Global sections of a geometric skyscraper

Let Ω be a separably closed field, X a scheme in universe u, and x : Spec(Ω) → X. For additive
groups of universe max(u,w), the global-section functor composed with the geometric skyscraper
functor is naturally isomorphic to the identity.

The identity étale object over X is terminal and its geometric fiber is a singleton. The
comparison takes a global section to its terminal-object value and then to the coefficient at
that fiber point. Its inverse gives the constant coefficient value on the terminal fiber, and
the comparison is natural in coefficient morphisms.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

private theorem skyscraperCompositionValue.{v}
    {A B C : AddCommGrpCat.{v}} {f : A ⟶ C} {g : A ⟶ B} {h : B ⟶ C}
    (hf : f = g ≫ h) (s : A) : f s = h (g s) := by
  simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom hf s

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}

/-- Let Ω be a separably closed field, X a scheme of universe u, and x : Spec(Ω) → X. For
coefficients in AddCommGrpCat.{max(u,w)}, there is a natural isomorphism x_* ⋙ Γ(X_et,−) ≅ Id.
The forward comparison evaluates a skyscraper global section on the terminal identity étale
object and projects from its singleton geometric fiber to the coefficient group. -/
def smallEtaleSkyscraperSectionsIso (x : Spec (.of Ω) ⟶ X) :
    (smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor
        (A := AddCommGrpCat.{max u w}) ⋙
      Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w} ≅
        𝟭 AddCommGrpCat.{max u w} := by
  let p := smallEtaleGeometricPointCommon.{u, w} x
  let T := Scheme.Etale.mk (𝟙 X)
  letI : Unique (p.fiber.obj T) := p.uniqueFiberObj T (identityEtaleIsTerminal X)
  let E := smallEtaleGlobalTerminalIso.{u, w} X
  refine NatIso.ofComponents
    (fun M => E.app (p.skyscraperSheafFunctor.obj M) ≪≫
      productUniqueIso (fun _ : p.fiber.obj T => M)) ?_
  intro M N f
  let ΓM := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
    (p.skyscraperSheafFunctor.obj M)
  let ΓN := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
    (p.skyscraperSheafFunctor.obj N)
  let PM : AddCommGrpCat.{max u w} := ∏ᶜ fun _ : p.fiber.obj T => M
  let PN : AddCommGrpCat.{max u w} := ∏ᶜ fun _ : p.fiber.obj T => N
  let a : ΓM ⟶ ΓN := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map
    (p.skyscraperSheafFunctor.map f)
  let eM : ΓM ⟶ PM := (E.app (p.skyscraperSheafFunctor.obj M)).hom
  let eN : ΓN ⟶ PN := (E.app (p.skyscraperSheafFunctor.obj N)).hom
  let πM : PM ⟶ M := (productUniqueIso (fun _ : p.fiber.obj T => M)).hom
  let πN : PN ⟶ N := (productUniqueIso (fun _ : p.fiber.obj T => N)).hom
  let b : PM ⟶ PN := CategoryTheory.Limits.Pi.map (fun _ : p.fiber.obj T => f)
  have he : a ≫ eN = eM ≫ b := E.hom.naturality (p.skyscraperSheafFunctor.map f)
  have hp : b ≫ πN = πM ≫ f := by
    simpa only [b, πM, πN, productUniqueIso_hom] using
      (Pi.map_π (fun _ : p.fiber.obj T => f) default)
  exact (Category.assoc a eN πN).symm.trans
    ((congrArg (fun h : ΓM ⟶ PN => h ≫ πN) he).trans
      ((Category.assoc eM b πN).trans
        ((congrArg (fun h : PM ⟶ N => eM ≫ h) hp).trans
          (Category.assoc eM πM f).symm)))

/-- For x : Spec(Ω) → X with Ω separably closed, M ∈ AddCommGrpCat.{max(u,w)}, and any z in the
geometric fiber over id_X, the forward map Γ(x_*M) → M is the terminal-section isomorphism
Γ(x_*M) → ∏_{Fiber_x(id_X)}M followed by projection π_z. The terminal fiber is a singleton, so
the formula is independent of z. -/
theorem smallEtaleSkyscraperSectionsIso_hom (x : Spec (.of Ω) ⟶ X)
    (M : AddCommGrpCat.{max u w})
    (z : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj (Scheme.Etale.mk (𝟙 X))) :
    (smallEtaleSkyscraperSectionsIso.{u, w} x).hom.app M =
      (smallEtaleGlobalTerminalIso.{u, w} X).hom.app
          ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor.obj M) ≫
        Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj
          (Scheme.Etale.mk (𝟙 X)) => M) z := by
  let p := smallEtaleGeometricPointCommon.{u, w} x
  let T := Scheme.Etale.mk (𝟙 X)
  let : Unique (p.fiber.obj T) := p.uniqueFiberObj T (identityEtaleIsTerminal X)
  change (smallEtaleGlobalTerminalIso.{u, w} X).hom.app
      (p.skyscraperSheafFunctor.obj M) ≫
      (productUniqueIso (fun _ : p.fiber.obj T => M)).hom = _
  rw [productUniqueIso_hom]
  exact congrArg
    (fun t : p.fiber.obj T => (smallEtaleGlobalTerminalIso.{u, w} X).hom.app
      (p.skyscraperSheafFunctor.obj M) ≫ Pi.π (fun _ : p.fiber.obj T => M) t)
    (Subsingleton.elim default z)

/-- Let Ω be a separably closed field of universe u, X a scheme of that universe, x : Spec(Ω) → X,
M ∈ AddCommGrpCat.{max(u,w)}, z ∈ Fiber_x(id_X), and s ∈ Γ(x_*M). The forward sections
comparison sends s to π_z of its value under the global-to-terminal-section isomorphism. Its
result is the coefficient in M at that terminal-fiber point. -/
theorem smallEtaleSkyscraperSectionsIso_hom_apply (x : Spec (.of Ω) ⟶ X)
    (M : AddCommGrpCat.{max u w})
    (z : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj (Scheme.Etale.mk (𝟙 X)))
    (s : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
      ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor.obj M)) :
    (smallEtaleSkyscraperSectionsIso.{u, w} x).hom.app M s =
      Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj
          (Scheme.Etale.mk (𝟙 X)) => M) z
        ((smallEtaleGlobalTerminalIso.{u, w} X).hom.app
          ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor.obj M) s) := by
  exact skyscraperCompositionValue (smallEtaleSkyscraperSectionsIso_hom.{u, w} x M z) s

/-- Let Ω be a separably closed field of universe u, X a scheme of that universe, x : Spec(Ω) → X,
M ∈ AddCommGrpCat.{max(u,w)}, and m∈M. For the global section s given by the inverse
skyscraper sections comparison, its terminal-object value has coordinate m at every
z∈Fiber_x(id_X). -/
theorem smallEtaleSkyscraperSectionsIso_inv_apply (x : Spec (.of Ω) ⟶ X)
    (M : AddCommGrpCat.{max u w})
    (z : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj (Scheme.Etale.mk (𝟙 X)))
    (m : M) :
    Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w} x).fiber.obj
        (Scheme.Etale.mk (𝟙 X)) => M) z
      ((smallEtaleGlobalTerminalIso.{u, w} X).hom.app
        ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor.obj M)
          ((smallEtaleSkyscraperSectionsIso.{u, w} x).inv.app M m)) = m := by
  have h := ConcreteCategory.congr_hom
    ((smallEtaleSkyscraperSectionsIso.{u, w} x).inv_hom_id_app M) m
  exact (smallEtaleSkyscraperSectionsIso_hom_apply.{u, w} x M z
    ((smallEtaleSkyscraperSectionsIso.{u, w} x).inv.app M m)).symm.trans
      (by simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h)

/-- Let Ω be a separably closed field, x : Spec(Ω) → X, f : M → N an additive-group map in
universe max(u,w), and e_M,e_N the global skyscraper section comparisons. For s ∈ Γ(x_*M),
e_N(Γ(x_*f)(s))=f(e_M(s)). This is naturality of the terminal-fiber evaluation isomorphism. -/
theorem smallEtaleSkyscraperSectionsIso_naturality (x : Spec (.of Ω) ⟶ X)
    {M N : AddCommGrpCat.{max u w}} (f : M ⟶ N)
    (s : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
      ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor.obj M)) :
    (smallEtaleSkyscraperSectionsIso.{u, w} x).hom.app N
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map
          ((smallEtaleGeometricPointCommon.{u, w} x).skyscraperSheafFunctor.map f) s) =
      f ((smallEtaleSkyscraperSectionsIso.{u, w} x).hom.app M s) := by
  simpa only [Functor.comp_map, Functor.id_map, ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom ((smallEtaleSkyscraperSectionsIso.{u, w} x).hom.naturality f) s

end AlgebraicGeometry.Scheme.DerivedSections
