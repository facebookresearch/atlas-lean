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
# Category of simplicial sets with a fixed vertex set

For a type `O`, an object consists of a simplicial set with a chosen identification
`X₀ ≃ O`. Morphisms preserve the vertex labels, so every underlying map is
vertex-bijective. Forgetting the labels is faithful, reflects isomorphisms, and detects
monomorphisms.

The discrete simplicial set on `O` is initial, and the nerve of the codiscrete category
on `O` is terminal. Pullbacks and pushouts are constructed from their underlying
simplicial-set diagrams. Binary products are pullbacks over the terminal codiscrete
object and consist of pairs of simplices with matching vertex labels. Reflection of
a given limit or colimit cone is stated for a nonempty index shape, with an explicit
chosen object of that shape.

Inner fibrations and categorical equivalences are defined by their underlying
simplicial maps. See Stevenson, Notes on the Joyal model structure,
arXiv:1810.05233, §§5.1 and 5.3.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet

/--
The condition that the degree-zero component of a simplicial map is a bijection.
-/
def IsVertexBijective {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  Function.Bijective (f.app (op ⦋0⦌))

/--
A simplicial map is vertex-bijective exactly when its map on zero-simplices is
bijective.
-/
theorem isVertexBijective_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsVertexBijective f ↔ Function.Bijective (f.app (op ⦋0⦌)) :=
  Iff.rfl

/--
The identity of every simplicial set is vertex-bijective.
-/
theorem isVertexBijective_id (X : SSet.{u}) : IsVertexBijective (𝟙 X) :=
  Function.bijective_id

/--
A composite of vertex-bijective simplicial maps is vertex-bijective.
-/
theorem IsVertexBijective.comp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsVertexBijective f) (hg : IsVertexBijective g) :
    IsVertexBijective (f ≫ g) := by
  rw [isVertexBijective_iff] at hf hg ⊢
  rw [NatTrans.comp_app]
  exact hg.comp hf

/--
If `A → B` is a monomorphism of simplicial sets, the opposite pushout inclusion
`C → B ∪_A C` is a monomorphism.
-/
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

/--
If `A → C` is a monomorphism of simplicial sets, the opposite pushout inclusion
`B → B ∪_A C` is a monomorphism.
-/
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

/--
A simplicial set `X` together with a chosen equivalence `X₀ ≃ O`, identifying
its vertex set with the fixed type `O`.
-/
structure FixedVertex (O : Type u) where
  /--
  The simplicial set underlying an object with fixed vertex set `O`.
  -/
  underlying : SSet.{u}
  /--
  The chosen equivalence from the underlying zero-simplices to the fixed vertex
  set `O`.
  -/
  vertexEquiv : underlying _⦋0⦌ ≃ O

namespace FixedVertex

variable {O : Type u} {X Y Z : FixedVertex O}

/--
A simplicial map from `X` to `Y` whose degree-zero component preserves each vertex
label: `e_Y(f₀(v)) = e_X(v)`.
-/
@[ext]
structure Hom (X Y : FixedVertex O) where
  /--
  The simplicial map underlying a morphism between objects with fixed vertex set.
  -/
  hom : X.underlying ⟶ Y.underlying
  /--
  For every vertex `v`, its image has the same label in `O`:
  `e_Y(f₀(v)) = e_X(v)`.
  -/
  w : ∀ v : X.underlying _⦋0⦌,
    Y.vertexEquiv (hom.app (op ⦋0⦌) v) = X.vertexEquiv v

/--
The category whose objects are simplicial sets with a chosen vertex identification
with `O` and whose morphisms preserve those labels, with simplicial-map composition.
-/
instance category : Category.{u} (FixedVertex O) where
  Hom X Y := FixedVertex.Hom X Y
  id X := ⟨𝟙 _, fun _ ↦ rfl⟩
  comp f g := ⟨f.hom ≫ g.hom, fun v ↦ by
    simpa using (g.w (f.hom.app (op ⦋0⦌) v)).trans (f.w v)⟩
  id_comp f := Hom.ext (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.hom)
  assoc f g h := Hom.ext (Category.assoc f.hom g.hom h.hom)

/--
The underlying simplicial map of the identity fixed-vertex morphism is the identity.
-/
@[simp]
lemma hom_id (X : FixedVertex O) : (𝟙 X : X ⟶ X).hom = 𝟙 X.underlying :=
  rfl

/--
The underlying map of a composite fixed-vertex morphism is the composite of its
underlying simplicial maps.
-/
@[simp]
lemma hom_comp {X Y Z : FixedVertex O} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

/--
Two fixed-vertex morphisms are equal if their underlying simplicial maps are equal.
-/
theorem hom_ext {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

variable (O) in
/--
The functor forgetting the chosen vertex identification and taking each morphism
to its underlying simplicial map.
-/
def forget : FixedVertex O ⥤ SSet.{u} where
  obj X := X.underlying
  map f := f.hom
  map_id _X := rfl
  map_comp _f _g := rfl

/--
The forgetful functor sends an object to its underlying simplicial set.
-/
@[simp]
lemma forget_obj (X : FixedVertex O) : (forget O).obj X = X.underlying :=
  rfl

/--
The forgetful functor sends a fixed-vertex morphism to its underlying simplicial map.
-/
@[simp]
lemma forget_map {X Y : FixedVertex O} (f : X ⟶ Y) :
    (forget O).map f = f.hom :=
  rfl

/--
The forgetful functor is faithful, since a fixed-vertex morphism is determined by
its underlying simplicial map.
-/
instance forget_faithful : (forget O).Faithful where
  map_injective h := hom_ext h

/--
A simplicial map satisfying `e_Y(f₀(v)) = e_X(v)` for every vertex determines
a morphism in the fixed-vertex category.
-/
def liftHom (f : X.underlying ⟶ Y.underlying)
    (h : ∀ v : X.underlying _⦋0⦌,
      Y.vertexEquiv (f.app (op ⦋0⦌) v) = X.vertexEquiv v) : X ⟶ Y :=
  ⟨f, h⟩

/--
The underlying simplicial map of `liftHom f h` is the specified map `f`.
-/
@[simp]
lemma liftHom_hom (f : X.underlying ⟶ Y.underlying)
    (h : ∀ v : X.underlying _⦋0⦌,
      Y.vertexEquiv (f.app (op ⦋0⦌) v) = X.vertexEquiv v) :
    (liftHom f h).hom = f :=
  rfl

/--
The equivalence between morphisms in the fixed-vertex category and simplicial maps
whose degree-zero components preserve the chosen vertex identifications.
-/
def homEquivCompatible :
    (X ⟶ Y) ≃ { f : X.underlying ⟶ Y.underlying //
      ∀ v : X.underlying _⦋0⦌,
        Y.vertexEquiv (f.app (op ⦋0⦌) v) = X.vertexEquiv v } where
  toFun f := ⟨f.hom, f.w⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
Every fixed-vertex morphism is vertex-bijective as a simplicial map, because its
zero component is the identity on `O` after the chosen identifications.
-/
theorem forget_map_isVertexBijective (f : X ⟶ Y) :
    IsVertexBijective ((forget O).map f) := by
  change IsVertexBijective f.hom
  rw [isVertexBijective_iff]
  refine ⟨fun a b hab ↦ X.vertexEquiv.injective ?_, fun b ↦
    ⟨X.vertexEquiv.symm (Y.vertexEquiv b), Y.vertexEquiv.injective ?_⟩⟩
  · rw [← f.w a, ← f.w b, hab]
  · rw [f.w]
    simp

/--
A fixed-vertex morphism sends the vertex labelled `o` in the source to the vertex
labelled `o` in the target.
-/
theorem hom_app_zero_symm_apply (f : X ⟶ Y) (o : O) :
    f.hom.app (op ⦋0⦌) (X.vertexEquiv.symm o) = Y.vertexEquiv.symm o := by
  apply Y.vertexEquiv.injective
  rw [f.w, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

set_option linter.unusedVariables false in
/--
The equivalence between the source and target vertex sets obtained as
`e_Y⁻¹ ∘ e_X`, agreeing with the zero component of the morphism.
-/
@[nolint unusedArguments]
def homAppZeroEquiv (f : X ⟶ Y) :
    (X.underlying _⦋0⦌) ≃ (Y.underlying _⦋0⦌) :=
  X.vertexEquiv.trans Y.vertexEquiv.symm

/--
The equivalence `homAppZeroEquiv f` sends each vertex to its image under the
degree-zero component of `f`.
-/
@[simp]
lemma homAppZeroEquiv_apply (f : X ⟶ Y) (v : X.underlying _⦋0⦌) :
    homAppZeroEquiv f v = f.hom.app (op ⦋0⦌) v := by
  apply Y.vertexEquiv.injective
  simp [homAppZeroEquiv, f.w v]

/--
The fixed-vertex forgetful functor reflects isomorphisms: the inverse of an
underlying simplicial isomorphism also preserves the vertex labels.
-/
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

/--
The constant simplicial set on `S`, with simplices `S` in every degree and every
simplicial operator the identity.
-/
abbrev discreteSSet (S : Type u) : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj S

/--
In every simplex degree, the simplices of the discrete simplicial set on `S`
are the elements of `S`.
-/
@[simp]
lemma discreteSSet_obj (S : Type u) (Δ : SimplexCategoryᵒᵖ) :
    (discreteSSet S).obj Δ = S :=
  rfl

/--
Every simplicial operator of the discrete simplicial set acts as the identity.
-/
@[simp]
lemma discreteSSet_map_apply (S : Type u) {Δ Δ' : SimplexCategoryᵒᵖ}
    (ψ : Δ ⟶ Δ') (s : (discreteSSet S).obj Δ) :
    (discreteSSet S).map ψ s = s :=
  rfl

/--
The simplicial map between constant diagrams induced by a function `g : S → T`,
acting by `g` in every degree.
-/
def discreteMap {S T : Type u} (g : S → T) :
    discreteSSet S ⟶ discreteSSet T where
  app _ := ↾g
  naturality _ _ _ := by
    ext s
    rfl

/--
The map between discrete simplicial sets induced by `g` acts by `g` in each degree.
-/
@[simp, nolint simpNF]
lemma discreteMap_app_apply {S T : Type u} (g : S → T)
    (Δ : SimplexCategoryᵒᵖ) (s : (discreteSSet S).obj Δ) :
    (discreteMap g).app Δ s = g s :=
  rfl

/--
A choice of vertex of `X` for each element of `S` gives a map from the discrete
simplicial set on `S` to `X`, taking each element to the corresponding constant
simplex in every degree.
-/
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

/--
In degree zero, the map from the discrete simplicial set evaluates to the chosen
vertex family.
-/
@[simp, nolint simpNF]
lemma fromDiscrete_app_zero {S : Type u} {X : SSet.{u}}
    (v : S → X.obj (op ⦋0⦌)) (s : (discreteSSet S).obj (op ⦋0⦌)) :
    (fromDiscrete v).app (op ⦋0⦌) s = v s := by
  change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op (v s) = v s
  rw [SimplexCategory.const_eq_id]
  simp

/--
The equivalence between the vertices of the nerve of the codiscrete category on
`S` and `S`, obtained by evaluating the vertex tuple at zero.
-/
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

/--
The codiscrete vertex identification is evaluation of the corresponding tuple
at its zero index.
-/
@[simp, nolint simpNF]
lemma codiscreteVertexEquiv_apply (S : Type u)
    (c : (CategoryTheory.Codiscrete.functorToSSet.obj S) _⦋0⦌) :
    codiscreteVertexEquiv S c =
      CategoryTheory.Codiscrete.equivFun c 0 :=
  rfl

/--
Restricting a codiscrete nerve simplex to vertex `i` and applying the vertex
identification gives the `i`-th object of its tuple.
-/
@[simp, nolint simpNF]
lemma codiscreteVertexEquiv_map_const (S : Type u)
    {Δ : SimplexCategoryᵒᵖ} (i : Fin (Δ.unop.len + 1))
    (c : (CategoryTheory.Codiscrete.functorToSSet.obj S).obj Δ) :
    codiscreteVertexEquiv S
        ((CategoryTheory.Codiscrete.functorToSSet.obj S).map
          (SimplexCategory.const ⦋0⦌ Δ.unop i).op c) =
      (c.obj i).as :=
  rfl

/--
Under the tuple identification, a simplicial operator of the codiscrete nerve acts
by precomposition with its monotone map on vertex indices.
-/
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

/--
The constant simplicial set on `O` with its identity vertex identification, as an
object of the fixed-vertex category.
-/
abbrev discreteObj (O : Type u) : FixedVertex O where
  underlying := discreteSSet O
  vertexEquiv := Equiv.refl O

/--
The nerve of the codiscrete category on `O`, with vertex identification by evaluation
at zero, as an object of the fixed-vertex category.
-/
abbrev codiscreteObj (O : Type u) : FixedVertex O where
  underlying := CategoryTheory.Codiscrete.functorToSSet.obj O
  vertexEquiv := codiscreteVertexEquiv O

/--
The morphism from the discrete object on `O` taking the constant simplex at `o`
to the constant simplex at the vertex of `X` labelled `o`.
-/
def fromDiscreteObj (X : FixedVertex O) : discreteObj O ⟶ X :=
  liftHom (fromDiscrete (fun o ↦ X.vertexEquiv.symm o)) (fun o ↦ by
    change X.vertexEquiv ((fromDiscrete _).app (op ⦋0⦌) o) = o
    rw [fromDiscrete_app_zero]
    simp)

/--
The underlying map of `fromDiscreteObj X` is the simplicial map from the discrete
set determined by the inverse vertex identification of `X`.
-/
@[simp]
lemma fromDiscreteObj_hom (X : FixedVertex O) :
    (fromDiscreteObj X).hom =
      fromDiscrete (fun o ↦ X.vertexEquiv.symm o) :=
  rfl

/--
The discrete simplicial set on `O` is initial in the fixed-vertex category, since
a morphism from it is determined by the required vertex labels.
-/
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

/--
The map from the underlying simplicial set of `X` to the codiscrete nerve on `O`
which sends each simplex to the tuple of labels of its vertices.
-/
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

/--
The `i`-th entry of the tuple of the codiscrete image of a simplex is the label
of its `i`-th vertex.
-/
@[simp, nolint simpNF]
lemma equivFun_toCodiscreteSSet_app_apply (X : FixedVertex O)
    {n : ℕ} (x : X.underlying _⦋n⦌) (i : Fin (n + 1)) :
    CategoryTheory.Codiscrete.equivFun
        ((toCodiscreteSSet X).app (op ⦋n⦌) x) i =
      X.vertexEquiv
        (X.underlying.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x) :=
  rfl

/--
The fixed-vertex morphism to the codiscrete object recording the labels of all
vertices of each simplex.
-/
def toCodiscreteObj (X : FixedVertex O) : X ⟶ codiscreteObj O :=
  liftHom (toCodiscreteSSet X) (fun v ↦ by
    change codiscreteVertexEquiv O ((toCodiscreteSSet X).app (op ⦋0⦌) v) =
      X.vertexEquiv v
    change X.vertexEquiv
        (X.underlying.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op v) =
      X.vertexEquiv v
    rw [SimplexCategory.const_eq_id]
    simp)

/--
The underlying map of `toCodiscreteObj X` is the vertex-label map to the codiscrete
nerve.
-/
@[simp]
lemma toCodiscreteObj_hom (X : FixedVertex O) :
    (toCodiscreteObj X).hom = toCodiscreteSSet X :=
  rfl

/--
The codiscrete nerve on `O` is terminal in the fixed-vertex category, since each
simplex must map to the tuple of its vertex labels.
-/
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

/--
The fixed-vertex category has an initial object, given by the discrete simplicial
set on `O`.
-/
instance hasInitial : HasInitial (FixedVertex O) :=
  IsInitial.hasInitial isInitialDiscreteObj

/--
The fixed-vertex category has a terminal object, given by the codiscrete nerve
on `O`.
-/
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

/--
For an index category with a specified object `j₀`, a cone in the fixed-vertex
category is limiting if its underlying simplicial-set cone is limiting. The mediating
map preserves labels by compatibility with the `j₀`-th cone leg.
-/
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

/--
For an index category with a specified object `j₀`, a cocone in the fixed-vertex
category is colimiting if its underlying simplicial-set cocone is colimiting. The
mediating map preserves labels using the vertex-bijective `j₀`-th cocone leg.
-/
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

/--
The fixed-vertex forgetful functor reflects pullback cones.
-/
instance reflectsLimitsOfShape_walkingCospan :
    ReflectsLimitsOfShape WalkingCospan (forget O) where
  reflectsLimit := ⟨fun hc ↦
    ⟨isLimit_of_forget_isLimit WalkingCospan.left hc⟩⟩

/--
The fixed-vertex forgetful functor reflects pushout cocones.
-/
instance reflectsColimitsOfShape_walkingSpan :
    ReflectsColimitsOfShape WalkingSpan (forget O) where
  reflectsColimit := ⟨fun hc ↦
    ⟨isColimit_of_forget_isColimit WalkingSpan.left hc⟩⟩

/--
The first projection of the simplicial pullback of two fixed-vertex morphisms is
bijective on zero-simplices.
-/
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

/--
The underlying simplicial pullback, with vertex label obtained by its first
projection and the first object's vertex identification.
-/
noncomputable abbrev pullbackObj (f : X ⟶ Z) (g : Y ⟶ Z) :
    FixedVertex O where
  underlying := pullback f.hom g.hom
  vertexEquiv :=
    (Equiv.ofBijective _ (bijective_pullback_fst_app_zero f g)).trans
      X.vertexEquiv

/--
The label of a pullback vertex is the label of its first projection.
-/
@[simp]
lemma pullbackObj_vertexEquiv_apply (f : X ⟶ Z) (g : Y ⟶ Z)
    (p : (pullbackObj f g).underlying _⦋0⦌) :
    (pullbackObj f g).vertexEquiv p =
      X.vertexEquiv ((pullback.fst f.hom g.hom).app (op ⦋0⦌) p) :=
  rfl

/--
The first morphism from the fixed-vertex pullback object to the first cospan object.
-/
noncomputable def pullbackFst (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullbackObj f g ⟶ X :=
  liftHom (pullback.fst f.hom g.hom) (fun p ↦
    (pullbackObj_vertexEquiv_apply f g p).symm)

/--
The second morphism from the fixed-vertex pullback object to the second cospan object,
preserving the common vertex labels.
-/
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

/--
The underlying map of the first fixed-vertex pullback projection is the first
simplicial pullback projection.
-/
@[simp]
lemma pullbackFst_hom (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackFst f g).hom = pullback.fst f.hom g.hom :=
  rfl

/--
The underlying map of the second fixed-vertex pullback projection is the second
simplicial pullback projection.
-/
@[simp]
lemma pullbackSnd_hom (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackSnd f g).hom = pullback.snd f.hom g.hom :=
  rfl

/--
The pullback cone with the underlying simplicial pullback as vertex and its two
vertex-compatible projections as legs.
-/
noncomputable def pullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) :
    PullbackCone f g :=
  PullbackCone.mk (pullbackFst f g) (pullbackSnd f g)
    (hom_ext pullback.condition)

/--
The cone of the constructed fixed-vertex pullback is a limit cone.
-/
@[nolint defsWithUnderscore]
noncomputable def pullbackCone_isLimit (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsLimit (pullbackCone f g) :=
  isLimit_of_forget_isLimit WalkingCospan.left
    ((isLimitMapConePullbackConeEquiv (forget O) _).symm
      (pullbackIsPullback f.hom g.hom))

/-- `SSet(O)` has pullbacks, computed in `SSet`. -/
instance (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  ⟨⟨pullbackCone f g, pullbackCone_isLimit f g⟩⟩

/--
The category of simplicial sets with fixed vertex set `O` has pullbacks, constructed
from the underlying simplicial pullbacks and their vertex identifications.
-/
instance hasPullbacks : HasPullbacks (FixedVertex O) :=
  hasPullbacks_of_hasLimit_cospan (FixedVertex O)

/--
The fixed-vertex category has binary products, obtained as pullbacks over its
terminal codiscrete object. Their simplices are pairs with matching vertex labels.
-/
instance hasBinaryProducts : HasBinaryProducts (FixedVertex O) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

/--
The left inclusion of the simplicial pushout of two fixed-vertex morphisms is
bijective on zero-simplices.
-/
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

/--
The underlying simplicial pushout, with vertex identification transported through
the left pushout inclusion from the left object's vertex identification.
-/
noncomputable abbrev pushoutObj (f : X ⟶ Y) (g : X ⟶ Z) :
    FixedVertex O where
  underlying := pushout f.hom g.hom
  vertexEquiv :=
    (Equiv.ofBijective _ (bijective_pushout_inl_app_zero f g)).symm.trans
      Y.vertexEquiv

/--
A vertex in the image of the left pushout inclusion has the same label as its
preimage in the left object.
-/
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

/--
The left inclusion into the fixed-vertex pushout object, preserving the vertex labels.
-/
noncomputable def pushoutInl (f : X ⟶ Y) (g : X ⟶ Z) :
    Y ⟶ pushoutObj f g :=
  liftHom (pushout.inl f.hom g.hom) (fun y ↦
    pushoutObj_vertexEquiv_inl_apply f g y)

/--
The right inclusion into the fixed-vertex pushout object, preserving the vertex labels.
-/
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

/--
The underlying map of the left fixed-vertex pushout inclusion is the left simplicial
pushout inclusion.
-/
@[simp]
lemma pushoutInl_hom (f : X ⟶ Y) (g : X ⟶ Z) :
    (pushoutInl f g).hom = pushout.inl f.hom g.hom :=
  rfl

/--
The underlying map of the right fixed-vertex pushout inclusion is the right simplicial
pushout inclusion.
-/
@[simp]
lemma pushoutInr_hom (f : X ⟶ Y) (g : X ⟶ Z) :
    (pushoutInr f g).hom = pushout.inr f.hom g.hom :=
  rfl

/--
The pushout cocone with the underlying simplicial pushout as vertex and its two
vertex-compatible inclusions as legs.
-/
noncomputable def pushoutCocone (f : X ⟶ Y) (g : X ⟶ Z) :
    PushoutCocone f g :=
  PushoutCocone.mk (pushoutInl f g) (pushoutInr f g)
    (hom_ext pushout.condition)

/--
The cocone of the constructed fixed-vertex pushout is a colimit cocone.
-/
@[nolint defsWithUnderscore]
noncomputable def pushoutCocone_isColimit (f : X ⟶ Y) (g : X ⟶ Z) :
    IsColimit (pushoutCocone f g) :=
  isColimit_of_forget_isColimit WalkingSpan.left
    ((isColimitMapCoconePushoutCoconeEquiv (forget O) _).symm
      (pushoutIsPushout f.hom g.hom))

/-- `SSet(O)` has pushouts, computed in `SSet`. -/
instance (f : X ⟶ Y) (g : X ⟶ Z) : HasPushout f g :=
  ⟨⟨pushoutCocone f g, pushoutCocone_isColimit f g⟩⟩

/--
The category of simplicial sets with fixed vertex set `O` has pushouts, constructed
from the underlying simplicial pushouts and their vertex identifications.
-/
instance hasPushouts : HasPushouts (FixedVertex O) :=
  hasPushouts_of_hasColimit_span (FixedVertex O)

/--
A fixed-vertex morphism is a monomorphism exactly when its underlying simplicial
map is a monomorphism.
-/
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

/--
The forgetful functor from fixed-vertex simplicial sets preserves monomorphisms.
-/
instance forget_preservesMonomorphisms :
    (forget O).PreservesMonomorphisms where
  preserves f hf := (mono_iff_mono_forget f).mp hf

end PullbacksPushouts

section Classes

/--
The morphism property of fixed-vertex maps whose underlying simplicial maps are
inner fibrations.
-/
def innerFibrations (O : Type u) : MorphismProperty (FixedVertex O) :=
  MorphismProperty.inverseImage SSet.innerFibrations (forget O)

/--
A fixed-vertex map belongs to `innerFibrations O` exactly when its underlying
simplicial map belongs to the ambient inner-fibration property.
-/
theorem innerFibrations_mem_iff (f : X ⟶ Y) :
    innerFibrations O f ↔ SSet.innerFibrations ((forget O).map f) :=
  Iff.rfl

/--
The morphism property of fixed-vertex maps whose underlying simplicial maps are
categorical equivalences.
-/
def categoricalEquivalences (O : Type u) :
    MorphismProperty (FixedVertex O) :=
  MorphismProperty.inverseImage SSet.categoricalEquivalences (forget O)

/--
A fixed-vertex map is a categorical equivalence in the fixed-vertex category exactly
when its underlying simplicial map is a categorical equivalence.
-/
theorem categoricalEquivalences_mem_iff (f : X ⟶ Y) :
    categoricalEquivalences O f ↔
      SSet.categoricalEquivalences ((forget O).map f) :=
  Iff.rfl

/--
A fixed-vertex morphism is a categorical equivalence exactly when its underlying
simplicial map is vertex-bijective and a categorical equivalence; vertex bijectivity
is already ensured by the fixed-label condition.
-/
theorem categoricalEquivalences_iff (f : X ⟶ Y) :
    categoricalEquivalences O f ↔
      IsVertexBijective ((forget O).map f) ∧
        SSet.categoricalEquivalences ((forget O).map f) :=
  ⟨fun h ↦ ⟨forget_map_isVertexBijective f, h⟩, fun h ↦ h.2⟩

end Classes

end FixedVertex

end SSet
