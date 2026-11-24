/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import MathlibExt.AlgebraicTopology.SimplicialSet.CodiscreteNerve
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CategoricalEquivalences

/-!
# Simplicial sets with a fixed vertex set: the category `SSet(O)`

The category itself is defined in §5.3 (the setup already used in §5.1,
where it is observed that inner horn inclusions, hence all inner
anodyne maps, are bijective on vertices):

> Let `sSet(O)` denote the subcategory of `sSet` whose objects consist
> of the simplicial sets whose set of `0`-simplices is equal to a fixed
> set `O`. The morphisms in `sSet(O)` are the simplicial maps which
> induce the identity on the set `O`. […] We will say that a map in
> `sSet(O)` is an inner fibration, or inner anodyne, or a categorical
> equivalence, or a trivial Kan fibration, just in case the underlying
> map of simplicial sets is such a map.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet

/-- A simplicial map is *vertex-bijective* (Stevenson says "bijective
on vertices" or "a bijection on objects") when its degree-`0`
component is a bijection. Inner horn inclusions, hence all inner
anodyne maps, have this property; by Theorem C of arXiv:1810.05233
together with being a monomorphism and a categorical equivalence it
characterises the inner anodyne maps. -/
def IsVertexBijective {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  Function.Bijective (f.app (op ⦋0⦌))

/-- Vertex-bijectivity unfolds to bijectivity of the degree-`0`
component. -/
theorem isVertexBijective_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsVertexBijective f ↔ Function.Bijective (f.app (op ⦋0⦌)) :=
  Iff.rfl

/-- Identity maps of simplicial sets are vertex-bijective. -/
theorem isVertexBijective_id (X : SSet.{u}) : IsVertexBijective (𝟙 X) :=
  Function.bijective_id

/-- A composite of vertex-bijective simplicial maps is
vertex-bijective. -/
theorem IsVertexBijective.comp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsVertexBijective f) (hg : IsVertexBijective g) :
    IsVertexBijective (f ≫ g) := by
  rw [isVertexBijective_iff] at hf hg ⊢
  rw [NatTrans.comp_app]
  exact hg.comp hf

/-- Pushouts of monomorphisms of simplicial sets are monomorphisms:
degreewise this is the corresponding fact in `Type`, transported
along the degree functors, which preserve pushouts. (Not yet in
Mathlib for functor categories; recorded here for the cobase-change
arguments of the inner model structure.) -/
theorem mono_pushout_inr_of_mono {A B C : SSet.{u}} (f : A ⟶ B)
    (g : A ⟶ C) [Mono f] : Mono (pushout.inr f g) := by
  rw [NatTrans.mono_iff_mono_app]
  intro Δ
  have hcol : IsColimit (PushoutCocone.map
      (PushoutCocone.mk (pushout.inl f g) (pushout.inr f g)
        pushout.condition)
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj Δ)) :=
    (isColimitMapCoconePushoutCoconeEquiv _ _).toFun
      (isColimitOfPreserves _ (pushoutIsPushout f g))
  exact Limits.Types.pushoutCocone_inr_mono_of_isColimit hcol

/-- The symmetric cobase-change statement: if `g` is a monomorphism
of simplicial sets, so is `pushout.inl f g`. -/
theorem mono_pushout_inl_of_mono {A B C : SSet.{u}} (f : A ⟶ B)
    (g : A ⟶ C) [Mono g] : Mono (pushout.inl f g) := by
  rw [NatTrans.mono_iff_mono_app]
  intro Δ
  have hcol : IsColimit (PushoutCocone.map
      (PushoutCocone.mk (pushout.inl f g) (pushout.inr f g)
        pushout.condition)
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj Δ)) :=
    (isColimitMapCoconePushoutCoconeEquiv _ _).toFun
      (isColimitOfPreserves _ (pushoutIsPushout f g))
  exact Limits.Types.pushoutCocone_inr_mono_of_isColimit
    (PushoutCocone.flipIsColimit hcol)

/-- A simplicial set with a fixed identification of its vertex set
with the fixed type `O`. Objects of Stevenson's category `sSet(O)`
(arXiv:1810.05233, §5.3), with the equality `X₀ = O` replaced by the
chosen equivalence `vertexEquiv`. -/
structure FixedVertex (O : Type u) where
  /-- The underlying simplicial set. -/
  underlying : SSet.{u}
  /-- The identification of the `0`-simplices with `O`. -/
  vertexEquiv : underlying _⦋0⦌ ≃ O

namespace FixedVertex

variable {O : Type u} {X Y Z : FixedVertex O}

/-- A morphism of fixed-vertex simplicial sets: a simplicial map whose
degree-`0` component is the identity on `O` after transport along the
vertex identifications, i.e. `e_Y(f₀ v) = e_X v` for every vertex `v`.
These are precisely the vertex-bijective maps compatible with the
identifications (see `forget_map_isVertexBijective` and
`homEquivCompatible`). -/
@[ext]
structure Hom (X Y : FixedVertex O) where
  /-- The underlying simplicial map. -/
  hom : X.underlying ⟶ Y.underlying
  /-- The underlying map induces the identity on `O` in degree `0`. -/
  w : ∀ v : X.underlying _⦋0⦌,
    Y.vertexEquiv (hom.app (op ⦋0⦌) v) = X.vertexEquiv v

/-- The category structure on `FixedVertex O`: morphisms are
vertex-identity simplicial maps (`FixedVertex.Hom`), composed as
simplicial maps. -/
instance category : Category.{u} (FixedVertex O) where
  Hom X Y := FixedVertex.Hom X Y
  id X := ⟨𝟙 _, fun _ ↦ rfl⟩
  comp f g := ⟨f.hom ≫ g.hom, fun v ↦ by
    simpa using (g.w (f.hom.app (op ⦋0⦌) v)).trans (f.w v)⟩
  id_comp f := Hom.ext (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.hom)
  assoc f g h := Hom.ext (Category.assoc f.hom g.hom h.hom)

/-- The underlying simplicial map of the identity morphism is the
identity. -/
@[simp]
lemma hom_id (X : FixedVertex O) : (𝟙 X : X ⟶ X).hom = 𝟙 X.underlying :=
  rfl

/-- The underlying simplicial map of a composite is the composite of
the underlying maps. -/
@[simp]
lemma hom_comp {X Y Z : FixedVertex O} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

/-- Two morphisms of fixed-vertex simplicial sets are equal when
their underlying simplicial maps are equal. -/
theorem hom_ext {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

variable (O) in
/-- The forgetful functor from fixed-vertex simplicial sets to
simplicial sets, forgetting the vertex identification. Stevenson's
inclusion `sSet(O) ⊆ sSet`. -/
def forget : FixedVertex O ⥤ SSet.{u} where
  obj X := X.underlying
  map f := f.hom
  map_id _X := rfl
  map_comp _f _g := rfl

/-- The forgetful functor on objects is the underlying simplicial
set. -/
@[simp]
lemma forget_obj (X : FixedVertex O) : (forget O).obj X = X.underlying :=
  rfl

/-- The forgetful functor on morphisms is the underlying simplicial
map. -/
@[simp]
lemma forget_map {X Y : FixedVertex O} (f : X ⟶ Y) :
    (forget O).map f = f.hom :=
  rfl

/-- The forgetful functor is faithful: a morphism of `SSet(O)` is
determined by its underlying simplicial map. -/
instance forget_faithful : (forget O).Faithful where
  map_injective h := hom_ext h

/-- Build a morphism in `SSet(O)` from a simplicial map satisfying the
degree-`0` compatibility. This is the constructor-level converse of
`forget`: the morphisms of `SSet(O)` are exactly the compatible
simplicial maps (cf. `homEquivCompatible`). -/
def liftHom (f : X.underlying ⟶ Y.underlying)
    (h : ∀ v : X.underlying _⦋0⦌,
      Y.vertexEquiv (f.app (op ⦋0⦌) v) = X.vertexEquiv v) : X ⟶ Y :=
  ⟨f, h⟩

/-- The underlying map of `liftHom f h` is `f`. -/
@[simp]
lemma liftHom_hom (f : X.underlying ⟶ Y.underlying)
    (h : ∀ v : X.underlying _⦋0⦌,
      Y.vertexEquiv (f.app (op ⦋0⦌) v) = X.vertexEquiv v) :
    (liftHom f h).hom = f :=
  rfl

/-- Morphisms `X ⟶ Y` in `SSet(O)` correspond bijectively to
simplicial maps `X ⟶ Y` satisfying the degree-`0` compatibility:
the forgetful functor is "fully faithful onto the compatible
(vertex-bijective, label-preserving) maps", by construction. -/
def homEquivCompatible :
    (X ⟶ Y) ≃ { f : X.underlying ⟶ Y.underlying //
      ∀ v : X.underlying _⦋0⦌,
        Y.vertexEquiv (f.app (op ⦋0⦌) v) = X.vertexEquiv v } where
  toFun f := ⟨f.hom, f.w⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every morphism in `SSet(O)` is vertex-bijective as a simplicial
map: in degree `0` it is conjugate, via the vertex identifications,
to the identity on `O`. -/
theorem forget_map_isVertexBijective (f : X ⟶ Y) :
    IsVertexBijective ((forget O).map f) := by
  change IsVertexBijective f.hom
  rw [isVertexBijective_iff]
  refine ⟨fun a b hab ↦ X.vertexEquiv.injective ?_, fun b ↦
    ⟨X.vertexEquiv.symm (Y.vertexEquiv b), Y.vertexEquiv.injective ?_⟩⟩
  · rw [← f.w a, ← f.w b, hab]
  · rw [f.w]
    simp

/-- A morphism in `SSet(O)` sends the vertex labelled `o` to the
vertex labelled `o`. -/
theorem hom_app_zero_symm_apply (f : X ⟶ Y) (o : O) :
    f.hom.app (op ⦋0⦌) (X.vertexEquiv.symm o) = Y.vertexEquiv.symm o := by
  apply Y.vertexEquiv.injective
  rw [f.w, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

set_option linter.unusedVariables false in
/-- The degree-`0` component of a morphism in `SSet(O)` is bijective,
with the expected formula for the associated equivalence. -/
@[nolint unusedArguments]
def homAppZeroEquiv (f : X ⟶ Y) :
    (X.underlying _⦋0⦌) ≃ (Y.underlying _⦋0⦌) :=
  X.vertexEquiv.trans Y.vertexEquiv.symm

/-- The equivalence `homAppZeroEquiv f` agrees with the degree-`0`
component of `f`. -/
@[simp]
lemma homAppZeroEquiv_apply (f : X ⟶ Y) (v : X.underlying _⦋0⦌) :
    homAppZeroEquiv f v = f.hom.app (op ⦋0⦌) v := by
  apply Y.vertexEquiv.injective
  simp [homAppZeroEquiv, f.w v]

/-- The forgetful functor reflects isomorphisms: if the underlying
simplicial map is an isomorphism, its inverse automatically satisfies
the degree-`0` compatibility. -/
instance forget_reflectsIsomorphisms : (forget O).ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    have : IsIso f.hom := hf
    have hinv : ∀ w : Y.underlying _⦋0⦌,
        X.vertexEquiv ((inv f.hom).app (op ⦋0⦌) w) = Y.vertexEquiv w := by
      intro w
      have h1 : f.hom.app (op ⦋0⦌) ((inv f.hom).app (op ⦋0⦌) w) = w := by
        have h := ConcreteCategory.congr_hom
          (congr_app (IsIso.inv_hom_id f.hom) (op ⦋0⦌)) w
        simp
      have h2 := f.w ((inv f.hom).app (op ⦋0⦌) w)
      rw [h1] at h2
      exact h2.symm
    exact ⟨⟨liftHom (inv f.hom) hinv,
      hom_ext (by simp [IsIso.hom_inv_id f.hom]),
      hom_ext (by simp [IsIso.inv_hom_id f.hom])⟩⟩

section DiscreteCodiscrete

/-- The discrete simplicial set on a type `S`: its simplices in every
degree are the elements of `S` (the constant simplices), and every
simplicial operator is the identity. This is the constant functor
`(Functor.const SimplexCategoryᵒᵖ).obj S`, i.e. the constant
presheaf on `S`. The definitional equalities
`discreteSSet_obj`/`discreteSSet_map_apply` below hold by `rfl` for
this model, as they did for the previous hand-built one. -/
abbrev discreteSSet (S : Type u) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj S

/-- The simplices of the discrete simplicial set are the elements of
the type, in every degree. -/
@[simp]
lemma discreteSSet_obj (S : Type u) (Δ : SimplexCategoryᵒᵖ) :
    (discreteSSet S).obj Δ = S :=
  rfl

/-- Simplicial operators of the discrete simplicial set act trivially. -/
@[simp]
lemma discreteSSet_map_apply (S : Type u) {Δ Δ' : SimplexCategoryᵒᵖ}
    (ψ : Δ ⟶ Δ') (s : (discreteSSet S).obj Δ) :
    (discreteSSet S).map ψ s = s :=
  rfl

/-- A function between types induces a map of discrete simplicial
sets, acting by the same function in every degree. -/
def discreteMap {S T : Type u} (g : S → T) :
    discreteSSet S ⟶ discreteSSet T where
  app _ := ↾g
  naturality _ _ _ := by
    ext s
    rfl

/-- The map induced between discrete simplicial sets acts degreewise
by the given function. -/
@[simp, nolint simpNF]
lemma discreteMap_app_apply {S T : Type u} (g : S → T)
    (Δ : SimplexCategoryᵒᵖ) (s : (discreteSSet S).obj Δ) :
    (discreteMap g).app Δ s = g s :=
  rfl

/-- A choice of vertex of `X` for every element of `S` determines a
map from the discrete simplicial set on `S` to `X`, sending the
constant simplex `s` in degree `Δ` to the constant simplex on the
chosen vertex (via the unique map `Δ.unop ⟶ ⦋0⦌` in
`SimplexCategory`). -/
def fromDiscrete {S : Type u} {X : SSet.{u}} (v : S → X.obj (op ⦋0⦌)) :
    discreteSSet S ⟶ X where
  app Δ := ↾fun s ↦ X.map (SimplexCategory.const Δ.unop ⦋0⦌ 0).op (v s)
  naturality := by
    intro Δ Δ' ψ
    ext s
    change X.map (SimplexCategory.const Δ'.unop ⦋0⦌ 0).op (v s) =
      X.map ψ (X.map (SimplexCategory.const Δ.unop ⦋0⦌ 0).op (v s))
    rw [← Functor.map_comp_apply]
    congr 1

/-- In degree `0`, the map out of a discrete simplicial set evaluates
to the chosen vertex. -/
@[simp, nolint simpNF]
lemma fromDiscrete_app_zero {S : Type u} {X : SSet.{u}}
    (v : S → X.obj (op ⦋0⦌)) (s : (discreteSSet S).obj (op ⦋0⦌)) :
    (fromDiscrete v).app (op ⦋0⦌) s = v s := by
  change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op (v s) = v s
  rw [SimplexCategory.const_eq_id]
  simp

/-- The codiscrete simplicial set on a type `S` is the nerve of the
codiscrete (indiscrete) category on `S`, i.e.
`CategoryTheory.Codiscrete.functorToSSet.obj S` (see
`MathlibExt.AlgebraicTopology.SimplicialSet.CodiscreteNerve`). Its
`n`-simplices are identified with tuples `Fin (n + 1) → S` by
`CategoryTheory.Codiscrete.equivFun` (`equivFun c i = (c.obj i).as`),
and the vertex identification and terminal-map API below are
formulated through `equivFun`. -/
def codiscreteVertexEquiv (S : Type u) :
    (CategoryTheory.Codiscrete.functorToSSet.obj S) _⦋0⦌ ≃ S where
  toFun c := CategoryTheory.Codiscrete.equivFun c 0
  invFun s := CategoryTheory.Codiscrete.equivFun.symm (fun _ ↦ s)
  left_inv c := by
    apply CategoryTheory.Codiscrete.equivFun.injective
    funext i
    simp only [Nat.reduceAdd, Fin.isValue, Equiv.apply_symm_apply]
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    rw [hi]
  right_inv s := by simp [CategoryTheory.Codiscrete.equivFun]

/-- The codiscrete vertex identification is `equivFun` evaluated at
`0`. -/
@[simp, nolint simpNF]
lemma codiscreteVertexEquiv_apply (S : Type u)
    (c : (CategoryTheory.Codiscrete.functorToSSet.obj S) _⦋0⦌) :
    codiscreteVertexEquiv S c =
      CategoryTheory.Codiscrete.equivFun c 0 :=
  rfl

/-- Evaluating a simplex of the codiscrete nerve at its `i`-th
vertex: the vertex identification of the restriction along
`const ⦋0⦌ _ i` is `(c.obj i).as`, i.e. `equivFun c i` in standard
degree. -/
@[simp, nolint simpNF]
lemma codiscreteVertexEquiv_map_const (S : Type u)
    {Δ : SimplexCategoryᵒᵖ} (i : Fin (Δ.unop.len + 1))
    (c : (CategoryTheory.Codiscrete.functorToSSet.obj S).obj Δ) :
    codiscreteVertexEquiv S
        ((CategoryTheory.Codiscrete.functorToSSet.obj S).map
          (SimplexCategory.const ⦋0⦌ Δ.unop i).op c) =
      (c.obj i).as :=
  rfl

/-- Simplicial operators of the codiscrete nerve act on `equivFun`
tuples by precomposition with the underlying monotone map. -/
@[simp, nolint simpNF]
lemma codiscreteEquivFun_map_apply (S : Type u) {m n : ℕ}
    (ψ : ⦋n⦌ ⟶ ⦋m⦌)
    (c : (CategoryTheory.Codiscrete.functorToSSet.obj S) _⦋m⦌)
    (k : Fin (n + 1)) :
    CategoryTheory.Codiscrete.equivFun
        ((CategoryTheory.Codiscrete.functorToSSet.obj S).map ψ.op c)
          k =
      CategoryTheory.Codiscrete.equivFun c (ψ.toOrderHom k) :=
  rfl

/-- The discrete object on `O` in `SSet(O)`: the discrete simplicial
set with its tautological vertex identification. It is the initial
object of `SSet(O)` (`isInitialDiscreteObj`). -/
abbrev discreteObj (O : Type u) : FixedVertex O where
  underlying := discreteSSet O
  vertexEquiv := Equiv.refl O

/-- The codiscrete object on `O` in `SSet(O)`: the codiscrete
simplicial set with evaluation at `0` as vertex identification. It is
the terminal object of `SSet(O)` (`isTerminalCodiscreteObj`). -/
abbrev codiscreteObj (O : Type u) : FixedVertex O where
  underlying := CategoryTheory.Codiscrete.functorToSSet.obj O
  vertexEquiv := codiscreteVertexEquiv O

/-- The canonical map from the discrete object to any object of
`SSet(O)`, sending the constant simplex on `o` to the constant
simplex on the vertex labelled `o`. -/
def fromDiscreteObj (X : FixedVertex O) : discreteObj O ⟶ X :=
  liftHom (fromDiscrete (fun o ↦ X.vertexEquiv.symm o)) (fun o ↦ by
    change X.vertexEquiv ((fromDiscrete _).app (op ⦋0⦌) o) = o
    rw [fromDiscrete_app_zero]
    simp)

/-- The underlying simplicial set of `fromDiscreteObj X` is
`fromDiscrete` applied to the labelling. -/
@[simp]
lemma fromDiscreteObj_hom (X : FixedVertex O) :
    (fromDiscreteObj X).hom =
      fromDiscrete (fun o ↦ X.vertexEquiv.symm o) :=
  rfl

/-- The discrete simplicial set on `O` is initial in `SSet(O)`: a map
out of it is forced to send the constant simplex on `o` to the
constant simplex on the vertex labelled `o`. -/
def isInitialDiscreteObj : IsInitial (discreteObj O) :=
  IsInitial.ofUniqueHom (fun X ↦ fromDiscreteObj X) (fun X f ↦ by
    apply hom_ext
    ext Δ o
    have hfo : f.hom.app (op ⦋0⦌) o = X.vertexEquiv.symm o := by
      rw [Equiv.eq_symm_apply]
      exact f.w o
    have hn' : f.hom.app Δ o =
        X.underlying.map (SimplexCategory.const Δ.unop ⦋0⦌ 0).op
          (f.hom.app (op ⦋0⦌) o) := by
      have hn := ConcreteCategory.congr_hom
        (f.hom.naturality (SimplexCategory.const Δ.unop ⦋0⦌ 0).op) o
      simpa using hn
    calc f.hom.app Δ o =
          X.underlying.map (SimplexCategory.const Δ.unop ⦋0⦌ 0).op
            (f.hom.app (op ⦋0⦌) o) := hn'
      _ = X.underlying.map (SimplexCategory.const Δ.unop ⦋0⦌ 0).op
            (X.vertexEquiv.symm o) := by rw [hfo]
      _ = (fromDiscreteObj X).hom.app Δ o := rfl)

/-- The canonical simplicial map to the codiscrete nerve: an
`n`-simplex maps to the nerve simplex whose `equivFun` tuple is the
labels of its vertices (`equivFun_toCodiscreteSSet_app_apply`). -/
def toCodiscreteSSet (X : FixedVertex O) :
    X.underlying ⟶ CategoryTheory.Codiscrete.functorToSSet.obj O where
  app Δ := ↾fun x => CategoryTheory.Codiscrete.functor
    (fun i ↦ X.vertexEquiv
      (X.underlying.map (SimplexCategory.const ⦋0⦌ Δ.unop i).op x))
  naturality := by
    intro Δ Δ' ψ
    ext x
    refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
    · apply CategoryTheory.Codiscrete.ext
      change X.vertexEquiv
          (X.underlying.map (SimplexCategory.const ⦋0⦌ Δ'.unop i).op
            (X.underlying.map ψ x)) =
        X.vertexEquiv
          (X.underlying.map (SimplexCategory.const ⦋0⦌ Δ.unop
            (ψ.unop.toOrderHom i)).op x)
      rw [← Functor.map_comp_apply]
      congr 2
    · rfl

/-- The canonical map to the codiscrete nerve records vertex labels:
the `equivFun` tuple of the image of an `n`-simplex `x` at `i` is
the label of the `i`-th vertex of `x`. -/
@[simp, nolint simpNF]
lemma equivFun_toCodiscreteSSet_app_apply (X : FixedVertex O)
    {n : ℕ} (x : X.underlying _⦋n⦌) (i : Fin (n + 1)) :
    CategoryTheory.Codiscrete.equivFun
        ((toCodiscreteSSet X).app (op ⦋n⦌) x) i =
      X.vertexEquiv
        (X.underlying.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x) :=
  rfl

/-- The canonical map from any object of `SSet(O)` to the codiscrete
object, recording the labels of the vertices of every simplex. -/
def toCodiscreteObj (X : FixedVertex O) : X ⟶ codiscreteObj O :=
  liftHom (toCodiscreteSSet X) (fun v ↦ by
    change codiscreteVertexEquiv O ((toCodiscreteSSet X).app (op ⦋0⦌) v) =
      X.vertexEquiv v
    change X.vertexEquiv
        (X.underlying.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op v) =
      X.vertexEquiv v
    rw [SimplexCategory.const_eq_id]
    simp)

/-- The underlying simplicial map of `toCodiscreteObj X` is
`toCodiscreteSSet X`. -/
@[simp]
lemma toCodiscreteObj_hom (X : FixedVertex O) :
    (toCodiscreteObj X).hom = toCodiscreteSSet X :=
  rfl

/-- The codiscrete simplicial set on `O` is terminal in `SSet(O)`:
a map to it is forced, simplex by simplex, to record the labels of
the vertices. -/
def isTerminalCodiscreteObj : IsTerminal (codiscreteObj O) :=
  IsTerminal.ofUniqueHom (fun X ↦ toCodiscreteObj X) (fun X f ↦ by
    apply hom_ext
    ext Δ x
    refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
    · have hn := ConcreteCategory.congr_hom
        (f.hom.naturality (SimplexCategory.const ⦋0⦌ Δ.unop i).op) x
      have hn' : f.hom.app (op ⦋0⦌)
          (X.underlying.map (SimplexCategory.const ⦋0⦌ Δ.unop i).op
            x) =
        (CategoryTheory.Codiscrete.functorToSSet.obj O).map
          (SimplexCategory.const ⦋0⦌ Δ.unop i).op (f.hom.app Δ x) := by
        simpa only [NatTrans.comp_app, types_comp,
          Function.comp_apply] using hn
      have h := congrArg (codiscreteVertexEquiv O) hn'
      have hw : codiscreteVertexEquiv O (f.hom.app (op ⦋0⦌)
          (X.underlying.map (SimplexCategory.const ⦋0⦌ Δ.unop i).op
            x)) =
          X.vertexEquiv
            (X.underlying.map (SimplexCategory.const ⦋0⦌ Δ.unop i).op
              x) :=
        f.w _
      apply CategoryTheory.Codiscrete.ext
      change ((f.hom.app Δ x).obj i).as =
        X.vertexEquiv
          (X.underlying.map (SimplexCategory.const ⦋0⦌ Δ.unop i).op x)
      rw [← hw, h]
      rfl
    · rfl)

/-- `SSet(O)` has an initial object, the discrete object on `O`. -/
instance hasInitial : HasInitial (FixedVertex O) :=
  IsInitial.hasInitial isInitialDiscreteObj

/-- `SSet(O)` has a terminal object, the codiscrete object on `O`. -/
instance hasTerminal : HasTerminal (FixedVertex O) :=
  IsTerminal.hasTerminal isTerminalCodiscreteObj

end DiscreteCodiscrete

section PullbacksPushouts

/-- In a limit pullback cone whose right-hand map is an isomorphism,
the first projection is an isomorphism. (Spelled out for an arbitrary
limit cone, for use after evaluating a simplicial pullback in
degree `0`.) -/
private theorem isIso_fst_of_isLimit {C : Type*} [Category C]
    {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (t : PullbackCone f g)
    (ht : IsLimit t) [IsIso g] : IsIso t.fst := by
  let l : X ⟶ t.pt :=
    PullbackCone.IsLimit.lift ht (𝟙 X) (f ≫ inv g) (by simp)
  have hl1 : l ≫ t.fst = 𝟙 X := by simp [l]
  have hl2 : t.fst ≫ l = 𝟙 t.pt := by
    apply PullbackCone.IsLimit.hom_ext ht
    · rw [Category.assoc, hl1, Category.comp_id, Category.id_comp]
    · have hsnd : l ≫ t.snd = f ≫ inv g := by simp [l]
      simp only [Category.id_comp]
      rw [Category.assoc, hsnd, ← Category.assoc, t.condition,
        Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact ⟨⟨l, hl2, hl1⟩⟩

/-- In a colimit pushout cocone whose right-hand map is an
isomorphism, the left coprojection is an isomorphism. -/
private theorem isIso_inl_of_isColimit {C : Type*} [Category C]
    {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (t : PushoutCocone f g)
    (ht : IsColimit t) [IsIso g] : IsIso t.inl := by
  let l : t.pt ⟶ Y :=
    PushoutCocone.IsColimit.desc ht (𝟙 Y) (inv g ≫ f) (by simp)
  have hl1 : t.inl ≫ l = 𝟙 Y := by simp [l]
  have hl2 : l ≫ t.inl = 𝟙 t.pt := by
    apply PushoutCocone.IsColimit.hom_ext ht
    · rw [← Category.assoc, hl1, Category.id_comp, Category.comp_id]
    · have hinr : t.inr ≫ l = inv g ≫ f := by simp [l]
      simp only [Category.comp_id]
      rw [← Category.assoc, hinr, Category.assoc, t.condition,
        ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  exact ⟨⟨l, hl1, hl2⟩⟩

/-- In a colimit pushout cocone whose left-hand map is an
isomorphism, the right coprojection is an isomorphism. -/
private theorem isIso_inr_of_isColimit {C : Type*} [Category C]
    {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (t : PushoutCocone f g)
    (ht : IsColimit t) [IsIso f] : IsIso t.inr := by
  let l : t.pt ⟶ Z :=
    PushoutCocone.IsColimit.desc ht (inv f ≫ g) (𝟙 Z) (by simp)
  have hl1 : t.inr ≫ l = 𝟙 Z := by simp [l]
  have hl2 : l ≫ t.inr = 𝟙 t.pt := by
    apply PushoutCocone.IsColimit.hom_ext ht
    · have hinl : t.inl ≫ l = inv f ≫ g := by simp [l]
      simp only [Category.comp_id]
      rw [← Category.assoc, hinl, Category.assoc, ← t.condition,
        ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    · rw [← Category.assoc, hl1, Category.id_comp, Category.comp_id]
  exact ⟨⟨l, hl1, hl2⟩⟩

/-- The forgetful functor reflects limits of diagrams indexed by a
nonempty shape: a cone in `SSet(O)` whose underlying cone in `SSet`
is a limit cone is a limit cone. Indeed the mediating simplicial map
is automatically compatible with the vertex identifications, by
compatibility of any single cone leg, and uniqueness follows from
faithfulness. This is the precise form, at the level of reflection,
of Stevenson's "limits are computed in `sSet`" (arXiv:1810.05233,
§5.3): reflection needs only a nonempty shape, whereas limits
themselves are computed in `SSet` only over nonempty connected
shapes — the terminal object and binary products are not (see the
module docstring). -/
@[nolint defsWithUnderscore]
def isLimit_of_forget_isLimit {J : Type v} [Category.{w} J]
    (j₀ : J) {K : J ⥤ FixedVertex O} {c : Cone K}
    (hc : IsLimit ((forget O).mapCone c)) : IsLimit c where
  lift s := liftHom (hc.lift ((forget O).mapCone s)) (fun v ↦ by
    have hπ := (c.π.app j₀).w
      ((hc.lift ((forget O).mapCone s)).app (op ⦋0⦌) v)
    have hpt : (c.π.app j₀).hom.app (op ⦋0⦌)
        ((hc.lift ((forget O).mapCone s)).app (op ⦋0⦌) v) =
        (s.π.app j₀).hom.app (op ⦋0⦌) v :=
      ConcreteCategory.congr_hom
        (congr_app (hc.fac ((forget O).mapCone s) j₀) (op ⦋0⦌)) v
    rw [hpt] at hπ
    exact hπ.symm.trans ((s.π.app j₀).w v))
  fac s j := hom_ext (hc.fac _ j)
  uniq s m hm := hom_ext (hc.uniq ((forget O).mapCone s) m.hom fun j ↦ by
    simpa using congrArg Hom.hom (hm j))

/-- The forgetful functor reflects colimits of diagrams indexed by a
nonempty shape: a cocone in `SSet(O)` whose underlying cocone in
`SSet` is a colimit cocone is a colimit cocone. The mediating
simplicial map is compatible with the vertex identifications because
any single cocone leg is surjective (indeed bijective) on vertices.
As for limits, reflection needs only a nonempty shape, whereas
colimits themselves are computed in `SSet` only over nonempty
connected shapes — the initial object and binary coproducts are not
(see the module docstring). -/
@[nolint defsWithUnderscore]
def isColimit_of_forget_isColimit {J : Type v} [Category.{w} J]
    (j₀ : J) {K : J ⥤ FixedVertex O} {c : Cocone K}
    (hc : IsColimit ((forget O).mapCocone c)) : IsColimit c where
  desc s := liftHom (hc.desc ((forget O).mapCocone s)) (fun v ↦ by
    obtain ⟨a, ha⟩ := (forget_map_isVertexBijective (c.ι.app j₀)).2 v
    have ha' : (c.ι.app j₀).hom.app (op ⦋0⦌) a = v := ha
    calc s.pt.vertexEquiv
          ((hc.desc ((forget O).mapCocone s)).app (op ⦋0⦌) v)
        = s.pt.vertexEquiv ((s.ι.app j₀).hom.app (op ⦋0⦌) a) := by
          rw [← ha']
          exact congrArg s.pt.vertexEquiv
            (ConcreteCategory.congr_hom
              (congr_app (hc.fac ((forget O).mapCocone s) j₀) (op ⦋0⦌)) a)
      _ = (K.obj j₀).vertexEquiv a := (s.ι.app j₀).w a
      _ = c.pt.vertexEquiv v := by
          rw [← ha']
          exact ((c.ι.app j₀).w a).symm)
  fac s j := hom_ext (hc.fac _ j)
  uniq s m hm := hom_ext (hc.uniq ((forget O).mapCocone s) m.hom fun j ↦ by
    simpa using congrArg Hom.hom (hm j))

/-- The forgetful functor reflects pullbacks. -/
instance reflectsLimitsOfShape_walkingCospan :
    ReflectsLimitsOfShape WalkingCospan (forget O) where
  reflectsLimit := ⟨fun hc ↦
    ⟨isLimit_of_forget_isLimit WalkingCospan.left hc⟩⟩

/-- The forgetful functor reflects pushouts. -/
instance reflectsColimitsOfShape_walkingSpan :
    ReflectsColimitsOfShape WalkingSpan (forget O) where
  reflectsColimit := ⟨fun hc ↦
    ⟨isColimit_of_forget_isColimit WalkingSpan.left hc⟩⟩

/-- Evaluation in degree `0` of the first projection of a simplicial
pullback of vertex-bijective maps is bijective: degree-`0` evaluation
preserves the pullback, and a pullback in `Type` of a bijection has
bijective first projection. -/
theorem bijective_pullback_fst_app_zero (f : X ⟶ Z) (g : Y ⟶ Z) :
    Function.Bijective ((pullback.fst f.hom g.hom).app (op ⦋0⦌)) := by
  have : IsIso (((evaluation SimplexCategoryᵒᵖ (Type u)).obj
      (op ⦋0⦌)).map g.hom) := by
    rw [isIso_iff_bijective]
    exact forget_map_isVertexBijective g
  have hlim : IsLimit (PullbackCone.map
      (PullbackCone.mk (pullback.fst f.hom g.hom)
        (pullback.snd f.hom g.hom) pullback.condition)
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌))) :=
    (isLimitMapConePullbackConeEquiv _ _).toFun
      (isLimitOfPreserves _ (pullbackIsPullback f.hom g.hom))
  have hi := isIso_fst_of_isLimit _ hlim
  exact (isIso_iff_bijective _).mp hi

/-- The pullback in `SSet(O)`, as an object: the simplicial pullback,
with vertex identification through the first projection (which is a
bijection on vertices). Pullbacks in `SSet(O)` are computed in `SSet`. -/
noncomputable abbrev pullbackObj (f : X ⟶ Z) (g : Y ⟶ Z) :
    FixedVertex O where
  underlying := pullback f.hom g.hom
  vertexEquiv :=
    (Equiv.ofBijective _ (bijective_pullback_fst_app_zero f g)).trans
      X.vertexEquiv

/-- The vertex identification of a pullback is computed through the
first projection. -/
@[simp]
lemma pullbackObj_vertexEquiv_apply (f : X ⟶ Z) (g : Y ⟶ Z)
    (p : (pullbackObj f g).underlying _⦋0⦌) :
    (pullbackObj f g).vertexEquiv p =
      X.vertexEquiv ((pullback.fst f.hom g.hom).app (op ⦋0⦌) p) :=
  rfl

/-- The first projection of the pullback in `SSet(O)`. -/
noncomputable def pullbackFst (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullbackObj f g ⟶ X :=
  liftHom (pullback.fst f.hom g.hom) (fun p ↦
    (pullbackObj_vertexEquiv_apply f g p).symm)

/-- The second projection of the pullback in `SSet(O)`: its vertex
compatibility follows from that of the first projection and the
pullback condition in degree `0`. -/
noncomputable def pullbackSnd (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullbackObj f g ⟶ Y :=
  liftHom (pullback.snd f.hom g.hom) (fun p ↦ by
    change Y.vertexEquiv ((pullback.snd f.hom g.hom).app (op ⦋0⦌) p) =
      (pullbackObj f g).vertexEquiv p
    rw [pullbackObj_vertexEquiv_apply]
    have hcond : f.hom.app (op ⦋0⦌)
        ((pullback.fst f.hom g.hom).app (op ⦋0⦌) p) =
        g.hom.app (op ⦋0⦌) ((pullback.snd f.hom g.hom).app (op ⦋0⦌) p) := by
      have h := ConcreteCategory.congr_hom
        (congr_app (pullback.condition (f := f.hom) (g := g.hom))
          (op ⦋0⦌)) p
      simpa only [NatTrans.comp_app, types_comp,
        Function.comp_apply] using h
    have h1 := f.w ((pullback.fst f.hom g.hom).app (op ⦋0⦌) p)
    have h2 := g.w ((pullback.snd f.hom g.hom).app (op ⦋0⦌) p)
    rw [hcond] at h1
    exact h2.symm.trans h1)

/-- The underlying simplicial map of `pullbackFst` is the simplicial
pullback projection. -/
@[simp]
lemma pullbackFst_hom (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackFst f g).hom = pullback.fst f.hom g.hom :=
  rfl

/-- The underlying simplicial map of `pullbackSnd` is the simplicial
pullback projection. -/
@[simp]
lemma pullbackSnd_hom (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackSnd f g).hom = pullback.snd f.hom g.hom :=
  rfl

/-- The pullback cone in `SSet(O)` on the vertex-bijective cospan,
with cone point `pullbackObj`. Its image under the forgetful functor
is the simplicial pullback cone. -/
noncomputable def pullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) :
    PullbackCone f g :=
  PullbackCone.mk (pullbackFst f g) (pullbackSnd f g)
    (hom_ext pullback.condition)

/-- The pullback cone in `SSet(O)` is a limit cone, by reflection
along the forgetful functor from the simplicial pullback. -/
@[nolint defsWithUnderscore]
noncomputable def pullbackCone_isLimit (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsLimit (pullbackCone f g) :=
  isLimit_of_forget_isLimit WalkingCospan.left
    ((isLimitMapConePullbackConeEquiv (forget O) _).symm
      (pullbackIsPullback f.hom g.hom))

/-- `SSet(O)` has pullbacks, computed in `SSet`. -/
instance (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  ⟨⟨pullbackCone f g, pullbackCone_isLimit f g⟩⟩

/-- `SSet(O)` has all pullbacks. -/
instance hasPullbacks : HasPullbacks (FixedVertex O) :=
  hasPullbacks_of_hasLimit_cospan (FixedVertex O)

/-- Binary products in `SSet(O)`, obtained from pullbacks and the
terminal codiscrete object: the product is the fibre product over
the codiscrete object, i.e. pairs of simplices with matching vertex
labels — not the product in `SSet`. -/
instance hasBinaryProducts : HasBinaryProducts (FixedVertex O) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

/-- Evaluation in degree `0` of the left coprojection of a simplicial
pushout of vertex-bijective maps is bijective. -/
theorem bijective_pushout_inl_app_zero (f : X ⟶ Y) (g : X ⟶ Z) :
    Function.Bijective ((pushout.inl f.hom g.hom).app (op ⦋0⦌)) := by
  have : IsIso (((evaluation SimplexCategoryᵒᵖ (Type u)).obj
      (op ⦋0⦌)).map g.hom) := by
    rw [isIso_iff_bijective]
    exact forget_map_isVertexBijective g
  have hcol : IsColimit (PushoutCocone.map
      (PushoutCocone.mk (pushout.inl f.hom g.hom)
        (pushout.inr f.hom g.hom) pushout.condition)
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌))) :=
    (isColimitMapCoconePushoutCoconeEquiv _ _).toFun
      (isColimitOfPreserves _ (pushoutIsPushout f.hom g.hom))
  have hi := isIso_inl_of_isColimit _ hcol
  exact (isIso_iff_bijective _).mp hi

/-- The pushout in `SSet(O)`, as an object: the simplicial pushout,
with vertex identification through the left coprojection (which is a
bijection on vertices). Pushouts in `SSet(O)` — in particular
pushouts along monomorphisms — are computed in `SSet`, and a
pushout of a monomorphism of simplicial sets is again a monomorphism
(degreewise in `Type`), hence a monomorphism in `SSet(O)` by
`mono_iff_mono_forget`. -/
noncomputable abbrev pushoutObj (f : X ⟶ Y) (g : X ⟶ Z) :
    FixedVertex O where
  underlying := pushout f.hom g.hom
  vertexEquiv :=
    (Equiv.ofBijective _ (bijective_pushout_inl_app_zero f g)).symm.trans
      Y.vertexEquiv

/-- The vertex identification of a pushout sends a vertex in the
image of the left coprojection to its label. -/
@[simp, nolint simpNF]
lemma pushoutObj_vertexEquiv_inl_apply (f : X ⟶ Y) (g : X ⟶ Z)
    (y : Y.underlying _⦋0⦌) :
    (pushoutObj f g).vertexEquiv
        ((pushout.inl f.hom g.hom).app (op ⦋0⦌) y) =
      Y.vertexEquiv y := by
  change Y.vertexEquiv
      ((Equiv.ofBijective _ (bijective_pushout_inl_app_zero f g)).symm
        ((pushout.inl f.hom g.hom).app (op ⦋0⦌) y)) = Y.vertexEquiv y
  congr 1
  exact Equiv.symm_apply_apply _ y

/-- The left coprojection of the pushout in `SSet(O)`. -/
noncomputable def pushoutInl (f : X ⟶ Y) (g : X ⟶ Z) :
    Y ⟶ pushoutObj f g :=
  liftHom (pushout.inl f.hom g.hom) (fun y ↦
    pushoutObj_vertexEquiv_inl_apply f g y)

/-- The right coprojection of the pushout in `SSet(O)`: its vertex
compatibility follows from that of the left coprojection, the
pushout condition in degree `0`, and vertex-bijectivity of `g`. -/
noncomputable def pushoutInr (f : X ⟶ Y) (g : X ⟶ Z) :
    Z ⟶ pushoutObj f g :=
  liftHom (pushout.inr f.hom g.hom) (fun z ↦ by
    have ha : g.hom.app (op ⦋0⦌) ((homAppZeroEquiv g).symm z) = z := by
      rw [← homAppZeroEquiv_apply]
      simp
    have hcond : (pushout.inl f.hom g.hom).app (op ⦋0⦌)
        (f.hom.app (op ⦋0⦌) ((homAppZeroEquiv g).symm z)) =
        (pushout.inr f.hom g.hom).app (op ⦋0⦌)
          (g.hom.app (op ⦋0⦌) ((homAppZeroEquiv g).symm z)) := by
      have h := ConcreteCategory.congr_hom
        (congr_app (pushout.condition (f := f.hom) (g := g.hom))
          (op ⦋0⦌)) ((homAppZeroEquiv g).symm z)
      simpa using h
    rw [ha] at hcond
    change (pushoutObj f g).vertexEquiv
        ((pushout.inr f.hom g.hom).app (op ⦋0⦌) z) = Z.vertexEquiv z
    rw [← hcond, pushoutObj_vertexEquiv_inl_apply, f.w]
    have h2 := g.w ((homAppZeroEquiv g).symm z)
    rw [ha] at h2
    exact h2.symm)

/-- The underlying simplicial map of `pushoutInl` is the simplicial
pushout coprojection. -/
@[simp]
lemma pushoutInl_hom (f : X ⟶ Y) (g : X ⟶ Z) :
    (pushoutInl f g).hom = pushout.inl f.hom g.hom :=
  rfl

/-- The underlying simplicial map of `pushoutInr` is the simplicial
pushout coprojection. -/
@[simp]
lemma pushoutInr_hom (f : X ⟶ Y) (g : X ⟶ Z) :
    (pushoutInr f g).hom = pushout.inr f.hom g.hom :=
  rfl

/-- The pushout cocone in `SSet(O)`, with cocone point `pushoutObj`.
Its image under the forgetful functor is the simplicial pushout
cocone. -/
noncomputable def pushoutCocone (f : X ⟶ Y) (g : X ⟶ Z) :
    PushoutCocone f g :=
  PushoutCocone.mk (pushoutInl f g) (pushoutInr f g)
    (hom_ext pushout.condition)

/-- The pushout cocone in `SSet(O)` is a colimit cocone, by
reflection along the forgetful functor from the simplicial pushout. -/
@[nolint defsWithUnderscore]
noncomputable def pushoutCocone_isColimit (f : X ⟶ Y) (g : X ⟶ Z) :
    IsColimit (pushoutCocone f g) :=
  isColimit_of_forget_isColimit WalkingSpan.left
    ((isColimitMapCoconePushoutCoconeEquiv (forget O) _).symm
      (pushoutIsPushout f.hom g.hom))

/-- `SSet(O)` has pushouts, computed in `SSet`. -/
instance (f : X ⟶ Y) (g : X ⟶ Z) : HasPushout f g :=
  ⟨⟨pushoutCocone f g, pushoutCocone_isColimit f g⟩⟩

/-- `SSet(O)` has all pushouts. -/
instance hasPushouts : HasPushouts (FixedVertex O) :=
  hasPushouts_of_hasColimit_span (FixedVertex O)

/-- A map in `SSet(O)` is a monomorphism if and only if its
underlying simplicial map is a monomorphism. The forward direction
compares kernel pairs: the kernel pair in `SSet(O)` is computed in
`SSet` (`pullbackCone`), a monomorphism has isomorphic first kernel
projection, functors preserve isomorphisms, and a simplicial map
with isomorphic first kernel projection is a monomorphism. The
backward direction is faithfulness of the forgetful functor.
Cf. Lemma 5.11 of arXiv:1810.05233 (whose lifting-property
formulation is a Additional obligations for the supporting result). -/
theorem mono_iff_mono_forget (f : X ⟶ Y) :
    Mono f ↔ Mono ((forget O).map f) := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ (forget O).mono_of_mono_map hf⟩
  have : Mono f := hf
  have hk : IsKernelPair f (pullbackFst f f) (pullbackSnd f f) :=
    IsPullback.of_isLimit' ⟨hom_ext pullback.condition⟩
      (pullbackCone_isLimit f f)
  have : IsIso (pullbackFst f f) := hk.isIso_of_mono
  have : IsIso (pullback.fst f.hom f.hom) :=
    Functor.map_isIso (forget O) (pullbackFst f f)
  exact (IsKernelPair.of_hasPullback f.hom).mono_of_isIso_fst

/-- The forgetful functor preserves monomorphisms (it also reflects
them, by faithfulness): monomorphisms in `SSet(O)` are exactly the
underlying monomorphisms. -/
instance forget_preservesMonomorphisms :
    (forget O).PreservesMonomorphisms where
  preserves f hf := (mono_iff_mono_forget f).mp hf

end PullbacksPushouts

section Classes

/-- Inner fibrations in `SSet(O)`: by Stevenson's convention
(arXiv:1810.05233, §5.3), a map in `SSet(O)` is an inner fibration
just in case its underlying simplicial map is one. Hence the inverse
image of `SSet.innerFibrations` along the forgetful functor. These
will be the fibrations of the inner model structure (the supporting result). -/
def innerFibrations (O : Type u) : MorphismProperty (FixedVertex O) :=
  MorphismProperty.inverseImage SSet.innerFibrations (forget O)

/-- Membership in `innerFibrations O` is by definition inner
fibration of the underlying simplicial map. -/
theorem innerFibrations_mem_iff (f : X ⟶ Y) :
    innerFibrations O f ↔ SSet.innerFibrations ((forget O).map f) :=
  Iff.rfl

/-- Categorical equivalences in `SSet(O)`: by Stevenson's convention,
a map in `SSet(O)` is a categorical equivalence just in case its
underlying simplicial map is one (every map in `SSet(O)` is already
vertex-bijective, cf. Theorem C of arXiv:1810.05233). These will be
the weak equivalences of the inner model structure (the supporting result). -/
def categoricalEquivalences (O : Type u) :
    MorphismProperty (FixedVertex O) :=
  MorphismProperty.inverseImage SSet.categoricalEquivalences (forget O)

/-- Membership in `categoricalEquivalences O` is by definition
categorical equivalence of the underlying simplicial map. -/
theorem categoricalEquivalences_mem_iff (f : X ⟶ Y) :
    categoricalEquivalences O f ↔
      SSet.categoricalEquivalences ((forget O).map f) :=
  Iff.rfl

/-- A map of `SSet(O)` is a categorical equivalence in `SSet(O)` if
and only if it is vertex-bijective (automatic in `SSet(O)`) and a
categorical equivalence in `SSet`. -/
theorem categoricalEquivalences_iff (f : X ⟶ Y) :
    categoricalEquivalences O f ↔
      IsVertexBijective ((forget O).map f) ∧
        SSet.categoricalEquivalences ((forget O).map f) :=
  ⟨fun h ↦ ⟨forget_map_isVertexBijective f, h⟩, fun h ↦ h.2⟩

end Classes

end FixedVertex

end SSet
