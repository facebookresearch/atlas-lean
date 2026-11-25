/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensor
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Finite dependent products as an unbiased tensor

A finite family of types is tensored by taking its dependent product, and morphisms act by
reindexing along their supplied bijections and applying the component maps. Singleton and
flattening equivalences satisfy the finite-tensor coherence laws and define a FiniteTensor
instance on Type u. The file gives evaluation formulas for these equivalences and proves
that the tensor of the empty family is terminal.
-/

@[expose] public section

namespace CategoryTheory.FiniteFamily

universe u

/-- Dependent product of a finite family of types. -/
def typeTensorObj (X : FiniteFamily (Type u)) : Type u :=
  (i : X.index) → X.obj i

/-- Map of dependent products via reindexing and pointwise maps. -/
def typeTensorMap {X Y : FiniteFamily (Type u)} (f : X ⟶ Y) :
    typeTensorObj X → typeTensorObj Y :=
  fun t => (Equiv.piCongrLeft Y.obj f.equiv) (fun x => f.hom x (t x))

/-- Application of `typeTensorMap` at an image index. -/
@[simp]
theorem typeTensorMap_apply {X Y : FiniteFamily (Type u)} (f : X ⟶ Y)
    (t : typeTensorObj X) (i : X.index) :
    typeTensorMap f t (f.equiv i) = f.hom i (t i) := by
  unfold typeTensorMap
  exact Equiv.piCongrLeft_apply_apply (P := Y.obj) (e := f.equiv)
    (f := fun x => f.hom x (t x)) i

/-- Application of `typeTensorMap` via `Equiv.piCongrLeft_apply_eq_cast`. -/
theorem typeTensorMap_apply_eq_cast {X Y : FiniteFamily (Type u)} (f : X ⟶ Y)
    (t : typeTensorObj X) (k : Y.index) :
    typeTensorMap f t k =
      cast (congr_arg Y.obj (f.equiv.apply_symm_apply k))
        (f.hom (f.equiv.symm k) (t (f.equiv.symm k))) := by
  unfold typeTensorMap
  rw [Equiv.piCongrLeft_apply_eq_cast]

/-- Functor `FiniteFamily (Type _) ⥤ Type _` given by dependent product. -/
def typeTensor : FiniteFamily (Type u) ⥤ Type u where
  obj X := typeTensorObj X
  map f := TypeCat.ofHom (typeTensorMap f)
  map_id X := by
    ext t
    funext j
    rfl
  map_comp {X Y Z} f g := by
    ext t
    funext k
    change typeTensorMap (Hom.comp f g) t k = typeTensorMap g (typeTensorMap f t) k
    obtain ⟨i, rfl⟩ := (f.equiv.trans g.equiv).surjective k
    have hf : (typeTensorMap f t) (f.equiv i) = f.hom i (t i) := by
      unfold typeTensorMap
      exact Equiv.piCongrLeft_apply_apply (P := Y.obj) (e := f.equiv)
        (f := fun a => f.hom a (t a)) i
    have hg : (typeTensorMap g (typeTensorMap f t)) (g.equiv (f.equiv i)) =
        g.hom (f.equiv i) ((typeTensorMap f t) (f.equiv i)) := by
      unfold typeTensorMap
      exact Equiv.piCongrLeft_apply_apply (P := Z.obj) (e := g.equiv)
        (f := fun y => g.hom y ((typeTensorMap f t) y)) (f.equiv i)
    change (Equiv.piCongrLeft Z.obj (f.equiv.trans g.equiv)
        (fun y => (f.hom y ≫ g.hom (f.equiv y)) (t y)) ((f.equiv.trans g.equiv) i)) =
      (Equiv.piCongrLeft Z.obj g.equiv
        (fun y => g.hom y ((typeTensorMap f t) y)) (g.equiv (f.equiv i)))
    have h1 : (Equiv.piCongrLeft Z.obj (f.equiv.trans g.equiv)
          (fun y => (f.hom y ≫ g.hom (f.equiv y)) (t y)) ((f.equiv.trans g.equiv) i))
        = (f.hom i ≫ g.hom (f.equiv i)) (t i) := by
            exact Equiv.piCongrLeft_apply_apply (P := Z.obj)
              (e := f.equiv.trans g.equiv) (a := i)
              (f := fun y => (f.hom y ≫ g.hom (f.equiv y)) (t y))
    have h2 : (f.hom i ≫ g.hom (f.equiv i)) (t i) =
        g.hom (f.equiv i) (f.hom i (t i)) := by
      rw [types_comp_apply]
    have h3 : g.hom (f.equiv i) (f.hom i (t i)) =
        g.hom (f.equiv i) ((typeTensorMap f t) (f.equiv i)) := by
      rw [congrArg (fun v => g.hom (f.equiv i) v) hf.symm]
    have h4 : g.hom (f.equiv i) ((typeTensorMap f t) (f.equiv i)) =
        (typeTensorMap g (typeTensorMap f t)) (g.equiv (f.equiv i)) := by
      rw [hg.symm]
    have h5 : (typeTensorMap g (typeTensorMap f t)) (g.equiv (f.equiv i)) =
        (Equiv.piCongrLeft Z.obj g.equiv
          (fun y => g.hom y ((typeTensorMap f t) y)) (g.equiv (f.equiv i))) := rfl
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

@[simp]
theorem typeTensor_obj (X : FiniteFamily (Type u)) :
    typeTensor.obj X = typeTensorObj X :=
  rfl

@[simp]
theorem typeTensor_map {X Y : FiniteFamily (Type u)} (f : X ⟶ Y) :
    typeTensor.map f = TypeCat.ofHom (typeTensorMap f) :=
  rfl

/-- Singleton equivalence for `Type`: `PUnit → X ≃ X`. -/
def typeTensorSingletonEquiv (X : Type u) : typeTensorObj (singleton.obj X) ≃ X :=
  Equiv.punitArrowEquiv X

@[simp]
theorem typeTensorSingletonEquiv_apply (X : Type u) (f : typeTensorObj (singleton.obj X)) :
    typeTensorSingletonEquiv X f = f PUnit.unit := rfl

@[simp]
theorem typeTensorSingletonEquiv_symm_apply (X : Type u) (x : X) (a : PUnit) :
    (typeTensorSingletonEquiv X).symm x a = x := rfl

/-- Singleton iso for the `Type` tensor functor. -/
def typeTensorSingletonIso : singleton (C := Type u) ⋙ typeTensor ≅ 𝟭 (Type u) :=
  NatIso.ofComponents (fun X => (typeTensorSingletonEquiv X).toIso) (by
    intro X Y f
    ext t
    rfl)

/-- Flatten equivalence for `Type`: dependent currying of a sigma index. -/
def typeTensorFlattenEquiv (X : FiniteFamily (FiniteFamily (Type u))) :
    typeTensorObj (flatten.obj X) ≃ typeTensorObj ((map typeTensor).obj X) :=
  Equiv.piCurry (fun a b => (X.obj a).obj b)

@[simp]
theorem typeTensorFlattenEquiv_apply (X : FiniteFamily (FiniteFamily (Type u)))
    (f : typeTensorObj (flatten.obj X)) (a : X.index) (b : (X.obj a).index) :
    typeTensorFlattenEquiv X f a b = f ⟨a, b⟩ := rfl

@[simp]
theorem typeTensorFlattenEquiv_symm_apply (X : FiniteFamily (FiniteFamily (Type u)))
    (g : typeTensorObj ((map typeTensor).obj X))
    (p : (a : X.index) × (X.obj a).index) :
    (typeTensorFlattenEquiv X).symm g p = g p.1 p.2 := rfl

/-- Flatten iso for the `Type` tensor functor. -/
def typeTensorFlattenIso :
    flatten (C := Type u) ⋙ typeTensor ≅
      (map typeTensor ⋙ typeTensor) :=
  NatIso.ofComponents (fun X => (typeTensorFlattenEquiv X).toIso) (by
    intro X Y f
    ext t
    funext a' b'
    obtain ⟨a, rfl⟩ := f.equiv.surjective a'
    obtain ⟨b, rfl⟩ := (f.hom a).equiv.surjective b'
    change typeTensorMap (flatten.map f) t ⟨f.equiv a, (f.hom a).equiv b⟩ =
      typeTensorMap ((map typeTensor).map f) (typeTensorFlattenEquiv X t) (f.equiv a)
        ((f.hom a).equiv b)
    have hLeft :
        typeTensorMap (flatten.map f) t ⟨f.equiv a, (f.hom a).equiv b⟩ =
          (f.hom a).hom b (t ⟨a, b⟩) := by
      have h := typeTensorMap_apply (flatten.map f) t ⟨a, b⟩
      change typeTensorMap (flatten.map f) t ⟨f.equiv a, (f.hom a).equiv b⟩ =
        (f.hom a).hom b (t ⟨a, b⟩) at h
      exact h
    have hInner :
        typeTensorMap (f.hom a) (typeTensorFlattenEquiv X t a)
            ((f.hom a).equiv b) =
          (f.hom a).hom b (typeTensorFlattenEquiv X t a b) :=
      typeTensorMap_apply (f.hom a) (typeTensorFlattenEquiv X t a) b
    have hOuter :
        typeTensorMap ((map typeTensor).map f) (typeTensorFlattenEquiv X t)
            (f.equiv a) =
          typeTensorMap (f.hom a) (typeTensorFlattenEquiv X t a) :=
      typeTensorMap_apply ((map typeTensor).map f) (typeTensorFlattenEquiv X t) a
    exact hLeft.trans
      ((congrArg (fun v => (f.hom a).hom b v)
          (typeTensorFlattenEquiv_apply X t a b).symm).trans
        (hInner.symm.trans
          (congrFun hOuter ((f.hom a).equiv b)).symm)))

instance : CategoryTheory.FiniteTensor (Type u) where
  tensor := typeTensor
  singletonIso := typeTensorSingletonIso
  flattenIso := typeTensorFlattenIso
  singletonFlattenLaw := by ext X t; rfl
  mapSingletonFlattenLaw := by ext X t; rfl
  flattenAssocLaw := by ext X t; rfl

/-- The `Type` singleton iso is the `PUnit`-arrow equivalence. -/
theorem types_singletonIso_eq : (FiniteTensor.singletonIso (V := Type u)) =
    typeTensorSingletonIso := rfl

/-- The `Type` flatten iso is dependent currying. -/
theorem types_flattenIso_eq : (FiniteTensor.flattenIso (V := Type u)) =
    typeTensorFlattenIso := rfl

/-- Singleton evaluation in `Type`. -/
theorem singleton_hom_apply_types (c : Type u)
    (g : (FiniteTensor.tensor (V := Type u)).obj
      ((singleton (C := Type u)).obj c)) :
    ((FiniteTensor.singletonIso (V := Type u)).hom.app c g) =
      g PUnit.unit := by
  rw [types_singletonIso_eq]
  exact typeTensorSingletonEquiv_apply c g

/-- Singleton introduction in `Type`. -/
theorem singleton_inv_apply_types (c : Type u) (x : c) :
    (((FiniteTensor.singletonIso (V := Type u)).inv.app c x)) PUnit.unit = x := by
  rw [types_singletonIso_eq]
  exact typeTensorSingletonEquiv_symm_apply c x PUnit.unit

/-- Currying in `Type`. -/
theorem flatten_hom_apply_types (N : FiniteFamily (FiniteFamily (Type u)))
    (f : (FiniteTensor.tensor (V := Type u)).obj
      ((flatten (C := Type u)).obj N))
    (a : N.index) (b : (N.obj a).index) :
    (((FiniteTensor.flattenIso (V := Type u)).hom.app N f) a b) =
      f ⟨a, b⟩ := by
  rw [types_flattenIso_eq]
  exact typeTensorFlattenEquiv_apply N f a b

/-- Uncurrying in `Type`. -/
theorem flatten_inv_apply_types (N : FiniteFamily (FiniteFamily (Type u)))
    (g : (FiniteTensor.tensor (V := Type u)).obj
      ((map (FiniteTensor.tensor (V := Type u))).obj N))
    (p : ((flatten (C := Type u)).obj N).index) :
    (((FiniteTensor.flattenIso (V := Type u)).inv.app N g)) p =
      g p.1 p.2 := by
  rw [types_flattenIso_eq]
  exact typeTensorFlattenEquiv_symm_apply N g p

universe w

/-- Interchange, hom direction: pushing a nested reindexing family
map through `flattenIso.hom`. Evaluating the curried flattened map
at reindexed indices equals the component map applied to the
curried input. This is `flattenIso` naturality at points, packaged
as one rewrite. -/
theorem typeTensorMap_flattenIso_hom_interchange
    {X Y : FiniteFamily (FiniteFamily (Type w))} (f : X ⟶ Y)
    (t : typeTensorObj (flatten.obj X)) (a : X.index)
    (b : (X.obj a).index) :
    (FiniteTensor.flattenIso (V := Type w)).hom.app Y
        (typeTensorMap (flatten.map f) t) (f.equiv a)
        ((f.hom a).equiv b)
      = (f.hom a).hom b
        ((FiniteTensor.flattenIso (V := Type w)).hom.app X t a b) := by
  have hflat : (FiniteTensor.flattenIso (V := Type w)).hom.app Y
        (typeTensorMap (flatten.map f) t) (f.equiv a)
        ((f.hom a).equiv b)
      = typeTensorMap (flatten.map f) t
        ⟨f.equiv a, (f.hom a).equiv b⟩ :=
    flatten_hom_apply_types Y _ _ _
  rw [hflat]
  have hmap : typeTensorMap (flatten.map f) t
        ⟨f.equiv a, (f.hom a).equiv b⟩
      = (f.hom a).hom b (t ⟨a, b⟩) :=
    typeTensorMap_apply (flatten.map f) t ⟨a, b⟩
  rw [hmap]
  have hcurry : (FiniteTensor.flattenIso (V := Type w)).hom.app X t a b
      = t ⟨a, b⟩ :=
    flatten_hom_apply_types X t a b
  rw [hcurry]

/-- Interchange, inv direction: pushing a nested reindexing family
map through `flattenIso.inv`. Uncurrying the mapped nested element
at a reindexed flattened index equals the component map applied to
the uncurried input. This is the direction consumed by
`graftEvaluationIso`, whose flatten head is `flattenIso.inv`. -/
theorem typeTensorMap_flattenIso_inv_interchange
    {X Y : FiniteFamily (FiniteFamily (Type w))} (f : X ⟶ Y)
    (s : typeTensorObj ((map typeTensor).obj X)) (a : X.index)
    (b : (X.obj a).index) :
    (FiniteTensor.flattenIso (V := Type w)).inv.app Y
        (typeTensorMap ((map typeTensor).map f) s)
        ((flatten.map f).equiv ⟨a, b⟩)
      = (f.hom a).hom b
        ((FiniteTensor.flattenIso (V := Type w)).inv.app X s
          ⟨a, b⟩) := by
  have hflat : (FiniteTensor.flattenIso (V := Type w)).inv.app Y
        (typeTensorMap ((map typeTensor).map f) s)
        ((flatten.map f).equiv ⟨a, b⟩)
      = typeTensorMap ((map typeTensor).map f) s (f.equiv a)
        ((f.hom a).equiv b) :=
    flatten_inv_apply_types Y _ _
  have hmap : typeTensorMap ((map typeTensor).map f) s (f.equiv a)
        ((f.hom a).equiv b)
      = (f.hom a).hom b (s a b) := by
    have h1 : typeTensorMap ((map typeTensor).map f) s (f.equiv a)
        = typeTensorMap (f.hom a) (s a) :=
      typeTensorMap_apply ((map typeTensor).map f) s a
    have h2 := congrFun h1 ((f.hom a).equiv b)
    exact h2.trans (typeTensorMap_apply (f.hom a) (s a) b)
  rw [hflat, hmap]
  have hcurry : (FiniteTensor.flattenIso (V := Type w)).inv.app X s
        ⟨a, b⟩
      = s a b :=
    flatten_inv_apply_types X s ⟨a, b⟩
  rw [hcurry]

/-- Any two elements of the canonical `Type` empty tensor agree: it
is the dependent product over the empty index. -/
theorem typeEmptyTensorUnique
    (a b : (FiniteTensor.tensor (V := Type u)).obj
      empty) :
    a = b := by
  funext i
  exact Empty.elim i

/-- Empty-tensor subterminality for the canonical `Type` tensor. -/
theorem typeEmptyTensorSubterminal (Z : Type u)
    (f g : Z ⟶ (FiniteTensor.tensor (V := Type u)).obj
      empty) :
    f = g := by
  ext z
  exact typeEmptyTensorUnique (f z) (g z)




end CategoryTheory.FiniteFamily
