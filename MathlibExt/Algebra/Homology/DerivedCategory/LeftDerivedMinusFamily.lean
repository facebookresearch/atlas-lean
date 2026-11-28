/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.DerivedCategory.LeftDerivedMinusNaturality

/-!
# Parameter families of bounded-above left-derived functors

Let C,D be abelian with the chosen derived categories of both categories
and their opposites, and suppose C has enough projectives.
An arbitrary parameter category I can index additive functors F_i:C → D.
Canonical derived transformations make their left-derived functors
L_i:D⁻(C) → D⁻(D) a family, or equivalently a bifunctor
I×D⁻(C) → D⁻(D).

The counits are natural in parameter maps, source-complex maps and
transformations between additive-functor families.
For a cochain complex K zero above d and projective in every degree,
the computation maps L_i([K]) → U_i(K) form a natural isomorphism
in i. Category, parameter and derived-category universes are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.DerivedCategory

universe uC vC uD vD uI vI wC wCo wD wDo

namespace DerivedCategory.CanonicalLeft.Family

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wCo} Cᵒᵖ]
  [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wDo} Dᵒᵖ]
  [EnoughProjectives C]
  {I : Type uI} [Category.{vI} I]
  (F : I ⥤ (C ⥤ D)) [∀ i : I, (F.obj i).Additive]

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

The derived family I → (D⁻(C) ⥤ D⁻(D)) sends i to L_i and a parameter map g to the derived natural
transformation of F(g). -/
def derived : I ⥤ (DerivedCategory.Minus C ⥤ DerivedCategory.Minus D) where
  obj i := CanonicalLeft.leftDerived (F.obj i)
  map f := Naturality.lift (F.map f)
  map_id i := by rw [F.map_id i, Naturality.lift_id]
  map_comp f g := by rw [F.map_comp f g, Naturality.lift_comp]

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

The bifunctor I×D⁻(C) → D⁻(D) has value L_i(X) on (i,X). -/
def bifunctor : I × DerivedCategory.Minus C ⥤ DerivedCategory.Minus D :=
  Functor.uncurry.obj (derived F)

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

The underived family sends i to U_i and parameter maps to the mapped-complex transformations
followed by localization. -/
def underived : I ⥤ (BoundedAboveDual.Complex C ⥤ DerivedCategory.Minus D) where
  obj i := CanonicalLeft.underived (F.obj i)
  map f := Naturality.underivedMap (F.map f)
  map_id i := by rw [F.map_id i, Naturality.underivedMap_id]
  map_comp f g := by rw [F.map_comp f g, Naturality.underivedMap_comp]

section FamilyMaps

variable {F} {G H : I ⥤ (C ⥤ D)} [∀ i : I, (G.obj i).Additive]
  [∀ i : I, (H.obj i).Additive]

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

A transformation τ:F → G between additive-functor families induces the natural family map with
component L(τ_i):L(F_i) → L(G_i). -/
def derivedMap (τ : F ⟶ G) : derived F ⟶ derived G where
  app i := Naturality.lift (τ.app i)
  naturality {i j} f := by
    exact (Naturality.lift_comp (F.map f) (τ.app j)).symm.trans
      ((congrArg Naturality.lift (τ.naturality f)).trans
        (Naturality.lift_comp (τ.app i) (G.map f)))

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

A transformation τ:F → G induces the corresponding natural map between the underived families U(F_i)
and U(G_i). -/
def underivedMap (τ : F ⟶ G) : underived F ⟶ underived G where
  app i := Naturality.underivedMap (τ.app i)
  naturality {i j} f := by
    exact (Naturality.underivedMap_comp (F.map f) (τ.app j)).symm.trans
      ((congrArg Naturality.underivedMap (τ.naturality f)).trans
        (Naturality.underivedMap_comp (τ.app i) (G.map f)))

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

The derived family map induced by the identity transformation of F is the identity of the derived
family. -/
theorem derivedMap_id : derivedMap (𝟙 F) = 𝟙 (derived F) := by
  apply NatTrans.ext
  funext i
  exact Naturality.lift_id (F.obj i)

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For transformations τ:F → G and σ:G → H of additive families, the derived map of σ∘τ equals the
composite of the two derived family maps. -/
theorem derivedMap_comp (τ : F ⟶ G) (σ : G ⟶ H) :
    derivedMap (τ ≫ σ) = derivedMap τ ≫ derivedMap σ := by
  apply NatTrans.ext
  funext i
  exact Naturality.lift_comp (τ.app i) (σ.app i)

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

The underived map induced by the identity transformation of F is the identity of its underived
family. -/
theorem underivedMap_id : underivedMap (𝟙 F) = 𝟙 (underived F) := by
  apply NatTrans.ext
  funext i
  exact Naturality.underivedMap_id (F.obj i)

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For transformations τ:F → G and σ:G → H, the underived family map of σ∘τ is the composite of their
underived maps. -/
theorem underivedMap_comp (τ : F ⟶ G) (σ : G ⟶ H) :
    underivedMap (τ ≫ σ) = underivedMap τ ≫ underivedMap σ := by
  apply NatTrans.ext
  funext i
  exact Naturality.underivedMap_comp (τ.app i) (σ.app i)

end FamilyMaps

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

At a fixed X∈D⁻(C), evaluation gives the family i↦L_i(X) in D⁻(D). -/
def atObject (X : DerivedCategory.Minus C) : I ⥤ DerivedCategory.Minus D :=
  derived F ⋙ (evaluation (DerivedCategory.Minus C) (DerivedCategory.Minus D)).obj X

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

At a fixed bounded-above model K∈C_-, evaluation gives the family i↦U_i(K) in D⁻(D). -/
def atComplex (K : BoundedAboveDual.Complex C) : I ⥤ DerivedCategory.Minus D :=
  underived F ⋙ (evaluation (BoundedAboveDual.Complex C) (DerivedCategory.Minus D)).obj K

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For K∈C_-, the counits ε_{i,K}:L_i(Q_CK) → U_i(K) form a natural transformation of parameter
families. -/
def counit (K : BoundedAboveDual.Complex C) :
    atObject F ((CanonicalLeft.Q C).obj K) ⟶ atComplex F K where
  app i := (CanonicalLeft.counit (F.obj i)).app K
  naturality {_ _} f := Naturality.counit_square_app (F.map f) K

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For f:K → M in C_-, the source map of evaluated derived families has component L_i(Q_Cf). -/
def sourceMap {K L : BoundedAboveDual.Complex C} (f : K ⟶ L) :
    atObject F ((CanonicalLeft.Q C).obj K) ⟶ atObject F ((CanonicalLeft.Q C).obj L) where
  app i := (CanonicalLeft.leftDerived (F.obj i)).map ((CanonicalLeft.Q C).map f)
  naturality {_ _} g := ((Naturality.lift (F.map g)).naturality ((CanonicalLeft.Q C).map f)).symm

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For f:K → M in C_-, the underived evaluated family map has component U_i(f). -/
def underivedSourceMap {K L : BoundedAboveDual.Complex C} (f : K ⟶ L) :
    atComplex F K ⟶ atComplex F L where
  app i := (CanonicalLeft.underived (F.obj i)).map f
  naturality {_ _} g := ((Naturality.underivedMap (F.map g)).naturality f).symm

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For f:K → M, the counit source square is ε_M∘L(Q_Cf)=U(f)∘ε_K as parameter-natural maps. -/
theorem sourceMap_counit {K L : BoundedAboveDual.Complex C} (f : K ⟶ L) :
    sourceMap F f ≫ counit F L = counit F K ≫ underivedSourceMap F f := by
  apply NatTrans.ext
  funext i
  exact (CanonicalLeft.counit (F.obj i)).naturality f

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

The evaluated derived-family source map of 1_K is the identity. -/
theorem sourceMap_id (K : BoundedAboveDual.Complex C) : sourceMap F (𝟙 K) = 𝟙 _ := by
  apply NatTrans.ext
  funext i
  exact (congrArg (CanonicalLeft.leftDerived (F.obj i)).map
    ((CanonicalLeft.Q C).map_id K)).trans
      ((CanonicalLeft.leftDerived (F.obj i)).map_id ((CanonicalLeft.Q C).obj K))

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For composable source maps f,g, the evaluated derived-family map of g∘f equals the composite of
their source maps. -/
theorem sourceMap_comp {K L M : BoundedAboveDual.Complex C} (f : K ⟶ L) (g : L ⟶ M) :
    sourceMap F (f ≫ g) = sourceMap F f ≫ sourceMap F g := by
  apply NatTrans.ext
  funext i
  exact (congrArg (CanonicalLeft.leftDerived (F.obj i)).map
    ((CanonicalLeft.Q C).map_comp f g)).trans
      ((CanonicalLeft.leftDerived (F.obj i)).map_comp
        ((CanonicalLeft.Q C).map f) ((CanonicalLeft.Q C).map g))

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

The evaluated underived-family source map of 1_K is the identity. -/
theorem underivedSourceMap_id (K : BoundedAboveDual.Complex C) :
    underivedSourceMap F (𝟙 K) = 𝟙 _ := by
  apply NatTrans.ext
  funext i
  exact (CanonicalLeft.underived (F.obj i)).map_id K

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For composable source maps f,g, the underived-family map of g∘f equals the composite of the two
source maps. -/
theorem underivedSourceMap_comp {K L M : BoundedAboveDual.Complex C}
    (f : K ⟶ L) (g : L ⟶ M) :
    underivedSourceMap F (f ≫ g) = underivedSourceMap F f ≫ underivedSourceMap F g := by
  apply NatTrans.ext
  funext i
  exact (CanonicalLeft.underived (F.obj i)).map_comp f g

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For g:i → j in I and f:K → M in C_-, the counit rectangle commutes:
ε_{j,M}∘L_j(Q_Cf)∘L(F(g))_{Q_CK}=U(F(g))_M∘U_i(f)∘ε_{i,K}. -/
theorem counit_parameter_source {i j : I} (g : i ⟶ j)
    {K L : BoundedAboveDual.Complex C} (f : K ⟶ L) :
    (atObject F ((CanonicalLeft.Q C).obj K)).map g ≫
        (sourceMap F f).app j ≫ (counit F L).app j =
      (counit F K).app i ≫ (underivedSourceMap F f).app i ≫ (atComplex F L).map g := by
  have hparam := (counit F K).naturality g
  have hsource := (CanonicalLeft.counit (F.obj j)).naturality f
  have hmap := (underivedSourceMap F f).naturality g
  calc
    _ = (atObject F ((CanonicalLeft.Q C).obj K)).map g ≫
        ((counit F K).app j ≫ (underivedSourceMap F f).app j) :=
      congrArg (fun a => (atObject F ((CanonicalLeft.Q C).obj K)).map g ≫ a) hsource
    _ = ((counit F K).app i ≫ (atComplex F K).map g) ≫
        (underivedSourceMap F f).app j :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ (underivedSourceMap F f).app j) hparam)
    _ = (counit F K).app i ≫
        ((underivedSourceMap F f).app i ≫ (atComplex F L).map g) :=
      (Category.assoc _ _ _).trans (congrArg (fun a => (counit F K).app i ≫ a) hmap)
    _ = _ := rfl

section CounitFamilyMaps

variable {F} {G : I ⥤ (C ⥤ D)} [∀ i : I, (G.obj i).Additive]

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For τ:F → G and X∈D⁻(C), the evaluated derived-family transformation has component L(τ_i)_X. -/
def mapAtObject (τ : F ⟶ G) (X : DerivedCategory.Minus C) : atObject F X ⟶ atObject G X :=
  Functor.whiskerRight (derivedMap τ)
    ((evaluation (DerivedCategory.Minus C) (DerivedCategory.Minus D)).obj X)

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For τ:F → G and K∈C_-, the evaluated underived-family transformation has component U(τ_i)_K. -/
def mapAtComplex (τ : F ⟶ G) (K : BoundedAboveDual.Complex C) : atComplex F K ⟶ atComplex G K :=
  Functor.whiskerRight (underivedMap τ)
    ((evaluation (BoundedAboveDual.Complex C) (DerivedCategory.Minus D)).obj K)

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For τ:F → G and K∈C_-, the evaluated derived and underived family maps commute with the canonical
counits: ε_G∘L(τ)_{Q_CK}=U(τ)_K∘ε_F. -/
theorem mapAtObject_counit (τ : F ⟶ G) (K : BoundedAboveDual.Complex C) :
    mapAtObject τ ((CanonicalLeft.Q C).obj K) ≫ counit G K =
      counit F K ≫ mapAtComplex τ K := by
  apply NatTrans.ext
  funext i
  exact Naturality.counit_square_app (τ.app i) K

end CounitFamilyMaps

variable (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d]

/-- For an abelian category C and an integer cochain complex K zero above
d∈ℤ, its object in the bounded-above model C_- is the opposite of
its degree-negating bounded-below Cᵒᵖ-reflection. -/
abbrev sourceComplex : BoundedAboveDual.Complex C :=
  BoundedAboveDual.ofBoundedAbove K d

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For a complex K zero above d, the comparison family L_i([K]) → U_i(K) is formed by the canonical
localization-model identification and the counit at K. -/
def comparison : atObject F (CanonicalLeft.objectOfBoundedAbove K d) ⟶
    atComplex F (sourceComplex K d) where
  app i := (CanonicalLeft.leftDerived (F.obj i)).map (CanonicalLeft.nativeLocalizationIso K d).inv ≫
    (CanonicalLeft.counit (F.obj i)).app (sourceComplex K d)
  naturality {i j} f := by
    let τ := F.map f
    let T := sourceComplex K d
    let X := CanonicalLeft.objectOfBoundedAbove K d
    let Y := (CanonicalLeft.Q C).obj T
    let e : Y ≅ X := CanonicalLeft.nativeLocalizationIso K d
    let Fi := CanonicalLeft.leftDerived (F.obj i)
    let Fj := CanonicalLeft.leftDerived (F.obj j)
    have h : (Naturality.lift τ).app X ≫ Fj.map e.inv =
        Fi.map e.inv ≫ (Naturality.lift τ).app Y :=
      ((Naturality.lift τ).naturality e.inv).symm
    have hc := Naturality.counit_square_app τ T
    calc
      _ = ((Naturality.lift τ).app X ≫ Fj.map e.inv) ≫
          (CanonicalLeft.counit (F.obj j)).app T := (Category.assoc _ _ _).symm
      _ = (Fi.map e.inv ≫ (Naturality.lift τ).app Y) ≫
          (CanonicalLeft.counit (F.obj j)).app T :=
        congrArg (fun a => a ≫ (CanonicalLeft.counit (F.obj j)).app T) h
      _ = Fi.map e.inv ≫ ((CanonicalLeft.counit (F.obj i)).app T ≫
          (Naturality.underivedMap τ).app T) :=
        (Category.assoc _ _ _).trans (congrArg (fun a => Fi.map e.inv ≫ a) hc)
      _ = _ := (Category.assoc _ _ _).symm

variable [∀ n : ℤ, Projective (K.X n)]

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For K zero above d and projective in every degree, the component of the computation comparison is an
isomorphism for every i∈I. -/
theorem comparison_isIso (i : I) : IsIso ((comparison F K d).app i) := by
  let Fi := F.obj i
  let T := sourceComplex K d
  let _ : IsIso ((BoundedAboveDual.counit Fi).app T) :=
    BoundedAboveDual.counit_isIso_of_projective Fi K d
  let G := (DerivedCategory.minusOppositeEquivalence D).inverse
  let ε := (BoundedAboveDual.counit Fi).app T
  let Y := (BoundedAboveDual.Q C).obj T
  let e := (CanonicalLeft.localizationComputationIso Fi).app Y ≪≫ G.mapIso (asIso ε)
  have hCounit : (CanonicalLeft.counit Fi).app T = e.hom := Naturality.counit_app Fi T
  let _ : IsIso ((CanonicalLeft.counit Fi).app T) :=
    hCounit.symm ▸ (inferInstance : IsIso e.hom)
  change IsIso ((CanonicalLeft.leftDerived Fi).map
    (CanonicalLeft.nativeLocalizationIso K d).inv ≫ (CanonicalLeft.counit Fi).app T)
  infer_instance

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For K zero above d and termwise projective, the computation maps form a natural isomorphism of
parameter families i↦L_i([K]) and i↦U_i(K). -/
def computationIso : atObject F (CanonicalLeft.objectOfBoundedAbove K d) ≅
    atComplex F (sourceComplex K d) :=
  NatIso.ofComponents (fun i => by
    let _ := comparison_isIso F K d i
    exact asIso ((comparison F K d).app i))
    (fun {i j} f => (comparison F K d).naturality f)

/-- Let C,D be abelian with independently chosen derived categories for
C,Cᵒᵖ,D,Dᵒᵖ, and C have enough projectives.
Let I be any parameter category and F:I → (C ⥤ D) a family with
each F_i additive. Write L_i:D⁻(C) → D⁻(D) for its canonical
left-derived functor, U_i:C_- → D⁻(D) for mapped-complex localization,
Q_C:C_- → D⁻(C), and ε_i:Q_C∘L_i → U_i for the counit.

For K zero above d and termwise projective, a parameter map g:i → j commutes with the forward
computation isomorphisms: c_j∘L(F(g))_{[K]}=U(F(g))_K∘c_i. -/
theorem computation_naturality {i j : I} (f : i ⟶ j) :
    (atObject F (CanonicalLeft.objectOfBoundedAbove K d)).map f ≫ (computationIso F K d).hom.app j =
      (computationIso F K d).hom.app i ≫ (atComplex F (sourceComplex K d)).map f :=
  (computationIso F K d).hom.naturality f

end DerivedCategory.CanonicalLeft.Family
