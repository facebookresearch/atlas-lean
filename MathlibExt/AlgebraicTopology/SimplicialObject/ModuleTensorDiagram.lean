/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor.Exact
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialQuasiIso

/-!
# Pointwise tensor diagrams and flat simplicial comparison

For simplicial modules `X` and `Y` over a commutative ring `k`, the pointwise tensor
diagram has degree-`n` term `X_n ⊗[k] Y_n`. It is the diagonal of the bisimplicial
diagram with outer degree from `Y` and inner degree from `X`, and its symmetry exchanges
the tensor factors without changing their simplicial degree.

A quasi-isomorphism of alternating-face complexes in one factor stays a quasi-isomorphism
when every degree of the other factor is flat. For simultaneous maps `f : X → X'` and
`g : Y → Y'`, flatness is needed on the source second factor `Y` and target first
factor `X'`. All module carriers here have height `max u v`, with the ground-ring
universe and the carrier parameter independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicTopology Opposite
open scoped TensorProduct Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.ModuleTensor

variable (k : Type u) [CommRing k]

/--
The simplicial module with terms `X_n ⊗[k] Y_n` and operators applying the
corresponding simplicial operator to both tensor factors.
-/
def diagram (X Y : SimplicialObject (ModuleCat.{max u v} k)) : SimplicialObject (ModuleCat.{max u v} k) where
  obj i := ModuleCat.tensorObjAt k (X.obj i) (Y.obj i)
  map θ := ModuleCat.tensorHomAt k (X.map θ) (Y.map θ)
  map_id i := by rw [X.map_id, Y.map_id]; exact ModuleCat.tensorHomAt_id k _ _
  map_comp θ η := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    simp only [CategoryTheory.Functor.map_comp, ModuleCat.tensorHomAt, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, LinearMap.comp_apply, TensorProduct.map_tmul]

/--
The map between pointwise tensor diagrams with degree-`n` component `f_n ⊗ g_n`.
-/
def map {X Y X' Y' : SimplicialObject (ModuleCat.{max u v} k)} (f : X ⟶ X') (g : Y ⟶ Y') :
    diagram k X Y ⟶ diagram k X' Y' where
  app i := ModuleCat.tensorHomAt k (f.app i) (g.app i)
  naturality {i j} θ := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    have hf := ConcreteCategory.congr_hom (f.naturality θ) x
    have hg := ConcreteCategory.congr_hom (g.naturality θ) y
    change (f.app j).hom ((X.map θ).hom x) = (X'.map θ).hom ((f.app i).hom x) at hf
    change (g.app j).hom ((Y.map θ).hom y) = (Y'.map θ).hom ((g.app i).hom y) at hg
    change (f.app j).hom ((X.map θ).hom x) ⊗ₜ[k] (g.app j).hom ((Y.map θ).hom y) =
      (X'.map θ).hom ((f.app i).hom x) ⊗ₜ[k] (Y'.map θ).hom ((g.app i).hom y)
    rw [hf, hg]

/--
The bisimplicial module with outer degree `p` and inner degree `q` equal to
`X_q ⊗[k] Y_p`; each direction acts only on its own tensor factor.
-/
def bisimplicial (X Y : SimplicialObject (ModuleCat.{max u v} k)) :
    SimplicialObject (SimplicialObject (ModuleCat.{max u v} k)) where
  obj j := X ⋙ (ModuleCat.tensorBifunctorAt k).flip.obj (Y.obj j)
  map θ :=
    { app i := ModuleCat.tensorHomAt k (𝟙 (X.obj i)) (Y.map θ)
      naturality {i i'} η := by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro x y
        rfl }
  map_id j := by
    apply NatTrans.ext
    funext i
    change ModuleCat.tensorHomAt k (𝟙 (X.obj i)) (Y.map (𝟙 j)) =
      𝟙 (ModuleCat.tensorObjAt k (X.obj i) (Y.obj j))
    rw [Y.map_id]
    exact ModuleCat.tensorHomAt_id k _ _
  map_comp θ η := by
    apply NatTrans.ext
    funext i
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change TensorProduct.map (LinearMap.id : X.obj i →ₗ[k] X.obj i) (Y.map (θ ≫ η)).hom
        (x ⊗ₜ[k] y) =
      TensorProduct.map (LinearMap.id : X.obj i →ₗ[k] X.obj i) (Y.map η).hom
        (TensorProduct.map (LinearMap.id : X.obj i →ₗ[k] X.obj i) (Y.map θ).hom (x ⊗ₜ[k] y))
    rw [Y.map_comp, ModuleCat.hom_comp]
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.comp_apply]

/--
The bisimplicial map with component `f_q ⊗ g_p` in outer degree `p` and inner
 degree `q`.
-/
def bisimplicialMap {X Y X' Y' : SimplicialObject (ModuleCat.{max u v} k)} (f : X ⟶ X') (g : Y ⟶ Y') :
    bisimplicial k X Y ⟶ bisimplicial k X' Y' where
  app j :=
    { app i := ModuleCat.tensorHomAt k (f.app i) (g.app j)
      naturality {i i'} θ := by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro x y
        have hf := ConcreteCategory.congr_hom (f.naturality θ) x
        change (f.app i').hom ((X.map θ).hom x) = (X'.map θ).hom ((f.app i).hom x) at hf
        change (f.app i').hom ((X.map θ).hom x) ⊗ₜ[k] (g.app j).hom y =
          (X'.map θ).hom ((f.app i).hom x) ⊗ₜ[k] (g.app j).hom y
        rw [hf] }
  naturality {j j'} θ := by
    apply NatTrans.ext
    funext i
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    have hg := ConcreteCategory.congr_hom (g.naturality θ) y
    change (g.app j').hom ((Y.map θ).hom y) = (Y'.map θ).hom ((g.app j).hom y) at hg
    change (f.app i).hom x ⊗ₜ[k] (g.app j').hom ((Y.map θ).hom y) =
      (f.app i).hom x ⊗ₜ[k] (Y'.map θ).hom ((g.app j).hom y)
    rw [hg]

/--
The simplicial isomorphism from the diagonal of the two-direction tensor diagram
to the pointwise diagram `X_n ⊗[k] Y_n`.
-/
def diagonalIso (X Y : SimplicialObject (ModuleCat.{max u v} k)) :
    (SimplicialObject.diagonalFunctor (ModuleCat.{max u v} k)).obj (bisimplicial k X Y) ≅ diagram k X Y :=
  NatIso.ofComponents (fun i => Iso.refl _) (by
    intro i j θ
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl)

/--
The diagonal identification commutes with the bisimplicial tensor map of `f` and
`g` and their pointwise tensor map.
-/
@[reassoc]
theorem diagonalIso_naturality {X Y X' Y' : SimplicialObject (ModuleCat.{max u v} k)} (f : X ⟶ X') (g : Y ⟶ Y') :
    (SimplicialObject.diagonalFunctor (ModuleCat.{max u v} k)).map (bisimplicialMap k f g) ≫
        (diagonalIso k X' Y').hom =
      (diagonalIso k X Y).hom ≫ map k f g := by
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

/--
The simplicial tensor-symmetry isomorphism `X ⊗[k] Y ≅ Y ⊗[k] X`, with each
component sending `x ⊗ y` to `y ⊗ x`.
-/
def commIso (X Y : SimplicialObject (ModuleCat.{max u v} k)) : diagram k X Y ≅ diagram k Y X :=
  NatIso.ofComponents (fun i => (TensorProduct.comm k (X.obj i) (Y.obj i)).toModuleIso) (by
    intro i j θ
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change TensorProduct.comm k (X.obj j) (Y.obj j)
        ((X.map θ).hom x ⊗ₜ[k] (Y.map θ).hom y) =
      TensorProduct.map (Y.map θ).hom (X.map θ).hom
        (TensorProduct.comm k (X.obj i) (Y.obj i) (x ⊗ₜ[k] y))
    simp only [TensorProduct.comm_tmul, TensorProduct.map_tmul])

/--
The tensor symmetry is natural in both simplicial factors:
`(f ⊗ g) ≫ symmetry = symmetry ≫ (g ⊗ f)`.
-/
@[reassoc]
theorem commIso_naturality {X Y X' Y' : SimplicialObject (ModuleCat.{max u v} k)} (f : X ⟶ X') (g : Y ⟶ Y') :
    map k f g ≫ (commIso k X' Y').hom = (commIso k X Y).hom ≫ map k g f := by
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change TensorProduct.comm k (X'.obj i) (Y'.obj i)
      ((f.app i).hom x ⊗ₜ[k] (g.app i).hom y) =
    TensorProduct.map (g.app i).hom (f.app i).hom
      (TensorProduct.comm k (X.obj i) (Y.obj i) (x ⊗ₜ[k] y))
  simp only [TensorProduct.comm_tmul, TensorProduct.map_tmul]

/--
An additive functor on modules that preserves homology sends a simplicial map
inducing an alternating-face quasi-isomorphism to another such map.
-/
theorem quasiIso_alternatingWhisker
    (F : (ModuleCat.{max u v} k) ⥤ (ModuleCat.{max u v} k)) [F.Additive] [F.PreservesHomology]
    {X X' : SimplicialObject (ModuleCat.{max u v} k)} (f : X ⟶ X')
    (hf : QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map f)) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map (Functor.whiskerRight f F)) := by
  letI := hf
  have h : QuasiIso ((F.mapHomologicalComplex (.down ℕ)).map
      ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map f)) :=
    inferInstance
  change QuasiIso ((((SimplicialObject.whiskering (ModuleCat.{max u v} k)
    (ModuleCat.{max u v} k)).obj F ⋙ alternatingFaceMapComplex (ModuleCat.{max u v} k)).map f))
  rw [← map_alternatingFaceMapComplex F]
  exact h

/--
If `f : X → X'` is an alternating-face quasi-isomorphism and every degree of `Y`
is flat over `k`, then the pointwise map `f ⊗ id_Y` is an alternating-face
quasi-isomorphism.
-/
theorem quasiIso_firstMap {X X' Y : SimplicialObject (ModuleCat.{max u v} k)} (f : X ⟶ X')
    (hf : QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map f))
    (hY : ∀ p : ℕ, Module.Flat k (Y.obj (op ⦋p⦌))) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map (map k f (𝟙 Y))) := by
  let φ := bisimplicialMap k f (𝟙 Y)
  have hφ : QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map
      ((SimplicialObject.diagonalFunctor (ModuleCat.{max u v} k)).map φ)) := by
    apply SimplicialObject.quasiIso_alternatingDiagonal_of_rows φ
    intro p
    letI : Module.Flat k (Y.obj (op ⦋p⦌)) := hY p
    let F := (ModuleCat.tensorBifunctorAt k).flip.obj (Y.obj (op ⦋p⦌))
    letI : F.PreservesHomology := ModuleCat.tensorBifunctorAt_flip_obj_preservesHomology k (Y.obj (op ⦋p⦌))
    have hrow : φ.app (op ⦋p⦌) = Functor.whiskerRight f F := by
      apply NatTrans.ext
      funext i
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      rfl
    rw [hrow]
    exact quasiIso_alternatingWhisker k F f hf
  let A := alternatingFaceMapComplex (ModuleCat.{max u v} k)
  letI := hφ
  have e := congrArg (fun t => A.map t) (diagonalIso_naturality k f (𝟙 Y))
  rw [A.map_comp, A.map_comp] at e
  letI : QuasiIso (A.map (diagonalIso k X Y).hom) := inferInstance
  have h : QuasiIso (A.map ((SimplicialObject.diagonalFunctor (ModuleCat.{max u v} k)).map φ) ≫
      A.map (diagonalIso k X' Y).hom) := inferInstance
  rw [e] at h
  letI := h
  exact quasiIso_of_comp_left (A.map (diagonalIso k X Y).hom) (A.map (map k f (𝟙 Y)))

/--
If `g : Y → Y'` is an alternating-face quasi-isomorphism and every degree of `X`
is flat over `k`, then the pointwise map `id_X ⊗ g` is an alternating-face
quasi-isomorphism.
-/
theorem quasiIso_secondMap {X Y Y' : SimplicialObject (ModuleCat.{max u v} k)} (g : Y ⟶ Y')
    (hg : QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map g))
    (hX : ∀ p : ℕ, Module.Flat k (X.obj (op ⦋p⦌))) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map (map k (𝟙 X) g)) := by
  let A := alternatingFaceMapComplex (ModuleCat.{max u v} k)
  letI : QuasiIso (A.map (map k g (𝟙 X))) := quasiIso_firstMap k g hg hX
  have e := congrArg (fun t => A.map t) (commIso_naturality k (𝟙 X) g)
  rw [A.map_comp, A.map_comp] at e
  have h : QuasiIso (A.map (map k (𝟙 X) g) ≫ A.map (commIso k X Y').hom) := by
    rw [e]
    infer_instance
  letI := h
  exact quasiIso_of_comp_right (A.map (map k (𝟙 X) g)) (A.map (commIso k X Y').hom)

/--
For alternating-face quasi-isomorphisms `f : X → X'` and `g : Y → Y'`, the map
`f ⊗ g` is an alternating-face quasi-isomorphism if every degree of `Y` and `X'`
is flat over `k`.
-/
theorem quasiIso_map {X X' Y Y' : SimplicialObject (ModuleCat.{max u v} k)} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map f))
    (hg : QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map g))
    (hY : ∀ p : ℕ, Module.Flat k (Y.obj (op ⦋p⦌)))
    (hX' : ∀ p : ℕ, Module.Flat k (X'.obj (op ⦋p⦌))) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map (map k f g)) := by
  have hcomp : map k f g = map k f (𝟙 Y) ≫ map k (𝟙 X') g := by
    apply NatTrans.ext
    funext i
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl
  letI := quasiIso_firstMap k f hf hY
  letI := quasiIso_secondMap k g hg hX'
  rw [hcomp, CategoryTheory.Functor.map_comp]
  infer_instance

end CategoryTheory.SimplicialObject.ModuleTensor
