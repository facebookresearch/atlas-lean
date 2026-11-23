/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaBaseChange
public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaHomology
public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedFiberHomology

/-!
# Naturality of the cofibered comma/fiber homology comparison

The homology of the covariant right-comma nerve diagram is naturally
isomorphic to the strict-fiber homology coefficient functor.  Naturality is
obtained by applying category homology to the direct-versus-iterated
cocartesian base-change isomorphism.

This supplies the rowwise coefficient comparison needed by the cofibered
Bousfield--Kan bicomplex.  It does not identify a spectral-sequence page or
assert convergence.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v vA uA

namespace CategoryTheory.Functor.IsCofibered

variable {S X : Type (max u v)} [Category.{v} S] [Category.{v} X]
  {p : X ⥤ S} [p.IsCofibered]
  (A : Type uA) [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{max u v} A] [CategoryWithHomology A]

/-- Homology of the covariant right-comma nerve diagram. -/
noncomputable def costructuredHomologyFunctor (R : A) (n : ℕ) : S ⥤ A :=
  CostructuredArrow.functor p ⋙ categoryHomologyFunctor A R n

omit [p.IsCofibered] in
@[simp]
theorem costructuredHomologyFunctor_obj (R : A) (n : ℕ) (s : S) :
    (costructuredHomologyFunctor (p := p) A R n).obj s =
      (nerve (CostructuredArrow p s)).homology R n :=
  rfl

omit [p.IsCofibered] in
@[simp]
theorem costructuredHomologyFunctor_map (R : A) (n : ℕ)
    {s t : S} (g : s ⟶ t) :
    (costructuredHomologyFunctor (p := p) A R n).map g =
      SSet.homologyMap (nerveMap (CostructuredArrow.map g)) R n :=
  rfl

/-- The objectwise right-comma/fiber homology isomorphisms commute with
base change. -/
theorem costructuredFiberHomologyIso_naturality
    {s t : S} (g : s ⟶ t) (R : A) (n : ℕ) :
    SSet.homologyMap (nerveMap (CostructuredArrow.map g)) R n ≫
        (costructuredFiberHomologyIso (p := p) A t R n).hom =
      (costructuredFiberHomologyIso (p := p) A s R n).hom ≫
        (fiberHomologyFunctor (p := p) A R n).map g := by
  let H : Cat.{v, max u v} ⥤ A := categoryHomologyFunctor A R n
  have hNat := categoryHomologyMap_eq_of_natIso A
    (costructuredToFiberBaseChangeIso (p := p) g) R n
  change H.map (CostructuredArrow.map g).toCatHom ≫
      H.map (costructuredToFiber (p := p) t).toCatHom =
    H.map (costructuredToFiber (p := p) s).toCatHom ≫
      H.map (fiberPushforwardFunctor (p := p) g).toCatHom
  calc
    _ = H.map ((CostructuredArrow.map g).toCatHom ≫
          (costructuredToFiber (p := p) t).toCatHom) :=
      (H.map_comp _ _).symm
    _ = H.map ((costructuredToFiber (p := p) s).toCatHom ≫
          (fiberPushforwardFunctor (p := p) g).toCatHom) := hNat
    _ = _ := H.map_comp _ _

/-- The right-comma homology diagram is naturally isomorphic to the strict-
fiber homology coefficient functor. -/
noncomputable def costructuredFiberHomologyNatIso (R : A) (n : ℕ) :
    costructuredHomologyFunctor (p := p) A R n ≅
      fiberHomologyFunctor (p := p) A R n :=
  by
    let F : S ⥤ A := costructuredHomologyFunctor (p := p) A R n
    let G : S ⥤ A := fiberHomologyFunctor (p := p) A R n
    let e : ∀ s : S, F.obj s ≅ G.obj s :=
      fun s => costructuredFiberHomologyIso (p := p) A s R n
    have h : ∀ {s t : S} (g : s ⟶ t),
        F.map g ≫ (e t).hom = (e s).hom ≫ G.map g := by
      intro s t g
      have hMap : F.map g =
          SSet.homologyMap (nerveMap (CostructuredArrow.map g)) R n :=
        costructuredHomologyFunctor_map (p := p) A R n g
      exact (congrArg
        (fun k : F.obj s ⟶ F.obj t => k ≫ (e t).hom) hMap).trans
          (costructuredFiberHomologyIso_naturality (p := p) A g R n)
    exact NatIso.ofComponents (F := F) (G := G) e h

end CategoryTheory.Functor.IsCofibered

end
