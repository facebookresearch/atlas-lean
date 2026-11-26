/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.RingChange
public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.ScalarChange
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Balanced tensor functors of enveloping-ring bimodules

Let R,S be arbitrary rings and B an E_(R,S)=R⊗[ℤ]Sᵒᵖ-module in
world b. Its endpoint actions make B an (R,S)-bimodule. Tensoring
a right R-module A in world a gives A⊗_R B as a right S-module
in world max(a,b), independently of the ring worlds.

The pairing is biadditive and balanced, and input maps act on the
first factor. Enveloping-module coefficient maps act on the second
factor, giving an additive functor from bimodules to tensor functors.

For φ:R→R′, ψ:S→S′ and a bimodule map B→Res_(φ,ψ)(B′),
the balanced map Res_(φᵒᵖ)(A′)⊗_R B→
Res_(ψᵒᵖ)(A′⊗_(R′)B′) sends [x⊗y] to [x⊗f(y)].
It is natural in the input and coefficient and coherent with
identity and composition of endpoint restrictions.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite
open scoped TensorProduct

universe r r' r'' s s' s'' a b

namespace ModuleCat.Bimodule.Tensor

variable (R : Type r) (S : Type s) [Ring R] [Ring S]

/-- For an E_(R,S)-module B and a right R-module A,
the object A⊗_R B carries its right S-action through B.
Its carrier world is max(a,b), without a bound on the ring worlds. -/
def obj (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) (A : ModuleCat.{a} Rᵐᵒᵖ) :
    ModuleCat.{max a b} Sᵐᵒᵖ := by
  letI := RingChange.leftModule R S B
  letI := RingChange.rightModule R S B
  letI := RingChange.commute R S B
  letI := TensorProduct.Balanced.rightModule ℤ R S A B
  exact ModuleCat.of Sᵐᵒᵖ (TensorProduct.Balanced ℤ R A B)

/-- For a right R-module A and an (R,S)-bimodule B,
the pairing (x,y)↦[x⊗y] is additive in both variables
and satisfies [(x·r)⊗y]=[x⊗(r·y)].
Its values lie in the right S-module A⊗_R B. -/
def pairing (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) (A : ModuleCat.{a} Rᵐᵒᵖ) :
    A →+ B →+ (obj R S B A).carrier := by
  letI := RingChange.leftModule R S B
  letI := RingChange.rightModule R S B
  letI := RingChange.commute R S B
  let h := TensorProduct.Balanced.mk ℤ R A B
  refine
    { toFun := fun x => (h x).toAddMonoidHom
      map_zero' := ?_
      map_add' := ?_ }
  · apply AddMonoidHom.ext
    intro y
    exact (h.flip y).map_zero
  · intro x x'
    apply AddMonoidHom.ext
    intro y
    exact LinearMap.congr_fun (h.map_add x x') y

/-- For a right R-linear map f:A→A′ and an (R,S)-bimodule B,
the induced right S-linear map A⊗_R B→A′⊗_R B sends
[x⊗y] to [f(x)⊗y]. -/
def map (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ))
    {A A' : ModuleCat.{a} Rᵐᵒᵖ} (f : A ⟶ A') : obj R S B A ⟶ obj R S B A' := by
  letI := RingChange.leftModule R S B
  letI := RingChange.rightModule R S B
  letI := RingChange.commute R S B
  letI := TensorProduct.Balanced.rightModule ℤ R S A B
  letI := TensorProduct.Balanced.rightModule ℤ R S A' B
  let f₀ : A →ₗ[ℤ] A' := f.hom.toAddMonoidHom.toIntLinearMap
  have hf : ∀ (r : R) (x : A), f₀ (op r • x) = op r • f₀ x := by
    intro r x
    exact f.hom.map_smul (op r) x
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.mapRight f₀ (LinearMap.id : B →ₗ[ℤ] B)
      hf (fun _ _ => rfl) (fun _ _ => rfl))

/-- For f:A→A′ right R-linear, the balanced pairing formula
for the induced map is [x⊗y]↦[f(x)⊗y].
The bimodule coefficient B is fixed. -/
theorem map_pairing (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ))
    {A A' : ModuleCat.{a} Rᵐᵒᵖ} (f : A ⟶ A') (x : A) (y : B) :
    (map R S B f).hom (pairing R S B A x y) =
      pairing R S B A' (f.hom x) y := rfl

/-- Two right S-linear maps from A⊗_R B to a module C
are equal if they agree on [x⊗y] for every x∈A,y∈B.
The source is a right R-module and B an (R,S)-bimodule. -/
theorem hom_ext (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) (A : ModuleCat.{a} Rᵐᵒᵖ)
    {C : ModuleCat.{max a b} Sᵐᵒᵖ} {f g : obj R S B A ⟶ C}
    (h : ∀ (x : A) (y : B), f.hom (pairing R S B A x y) =
      g.hom (pairing R S B A x y)) : f = g := by
  letI := RingChange.leftModule R S B
  letI := RingChange.rightModule R S B
  letI := RingChange.commute R S B
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  exact TensorProduct.Balanced.addHom_ext ℤ R A B h

/-- For an E_(R,S)-module B in world b, balanced tensor
defines ModuleCat^a(Rᵒᵖ)→ModuleCat^max(a,b)(Sᵒᵖ),
A↦A⊗_R B. It sends input maps to their first-factor tensor maps. -/
def functor (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) :
    ModuleCat.{a} Rᵐᵒᵖ ⥤ ModuleCat.{max a b} Sᵐᵒᵖ where
  obj := obj R S B
  map := map R S B
  map_id A := by
    apply hom_ext R S B A
    intro x y
    rw [map_pairing]
    rfl
  map_comp {A A' A''} f g := by
    apply hom_ext R S B A
    intro x y
    change (map R S B (f ≫ g)).hom (pairing R S B A x y) =
      (map R S B g).hom ((map R S B f).hom (pairing R S B A x y))
    rw [map_pairing, map_pairing, map_pairing]
    rfl

/-- For a fixed (R,S)-bimodule B, the functor A↦A⊗_R B
preserves addition of right R-linear input morphisms.
Its pure values are additive in the first factor. -/
instance functor_additive (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)) :
    (functor R S B).Additive where
  map_add {A A' f g} := by
    apply hom_ext R S B A
    intro x y
    change (map R S B (f + g)).hom (pairing R S B A x y) =
      ((map R S B f).hom + (map R S B g).hom) (pairing R S B A x y)
    rw [LinearMap.add_apply, map_pairing, map_pairing, map_pairing,
      ModuleCat.hom_add, LinearMap.add_apply]
    exact DFunLike.congr_fun ((pairing R S B A').map_add (f.hom x) (g.hom x)) y

section Coefficients

variable {B B' B'' : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)}

/-- For an enveloping-module morphism f:B→B′ and a right
R-module A, the map A⊗_R B→A⊗_R B′ is right S-linear
and applies f to the coefficient factor. -/
def coefficientMap (f : B ⟶ B') (A : ModuleCat.{a} Rᵐᵒᵖ) :
    obj R S B A ⟶ obj R S B' A := by
  letI := RingChange.leftModule R S B
  letI := RingChange.rightModule R S B
  letI := RingChange.commute R S B
  letI := RingChange.leftModule R S B'
  letI := RingChange.rightModule R S B'
  letI := RingChange.commute R S B'
  letI := TensorProduct.Balanced.rightModule ℤ R S A B
  letI := TensorProduct.Balanced.rightModule ℤ R S A B'
  let f₀ : B →ₗ[ℤ] B' := f.hom.toAddMonoidHom.toIntLinearMap
  have hL : ∀ (r : R) (y : B), f₀ (r • y) = r • f₀ y := by
    intro r y
    change f.hom ((r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ)) • y) =
      (r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ)) • f.hom y
    exact f.hom.map_smul (r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ)) y
  have hR : ∀ (t : Sᵐᵒᵖ) (y : B), f₀ (t • y) = t • f₀ y := by
    intro t y
    change f.hom (((1 : R) ⊗ₜ[ℤ] t) • y) =
      ((1 : R) ⊗ₜ[ℤ] t) • f.hom y
    exact f.hom.map_smul ((1 : R) ⊗ₜ[ℤ] t) y
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.mapRight (LinearMap.id : A →ₗ[ℤ] A) f₀
      (fun _ _ => rfl) hL hR)

/-- For a bimodule morphism f:B→B′, the coefficient map
sends the balanced class [x⊗y] to [x⊗f(y)].
The right R-module input A is unchanged. -/
theorem coefficientMap_pairing (f : B ⟶ B') (A : ModuleCat.{a} Rᵐᵒᵖ)
    (x : A) (y : B) :
    (coefficientMap R S f A).hom (pairing R S B A x y) =
      pairing R S B' A x (f.hom y) := rfl

/-- For an E_(R,S)-module map f:B→B′, the coefficient
maps A⊗_R B→A⊗_R B′ are natural in the right R-module A.
They define a transformation between the two tensor functors. -/
def coefficientTransformation (f : B ⟶ B') : functor R S B ⟶ functor R S B' where
  app := coefficientMap R S f
  naturality {A A'} g := by
    apply hom_ext R S B A
    intro x y
    change (coefficientMap R S f A').hom
        ((map R S B g).hom (pairing R S B A x y)) =
      (map R S B' g).hom
        ((coefficientMap R S f A).hom (pairing R S B A x y))
    rw [map_pairing, coefficientMap_pairing, coefficientMap_pairing, map_pairing]

/-- The coefficient transformation of id_B is the identity
on the balanced tensor functor −⊗_R B.
It fixes every pure class [x⊗y]. -/
theorem coefficientTransformation_id :
    coefficientTransformation R S (𝟙 B : B ⟶ B) = 𝟙 (functor R S B) := by
  apply NatTrans.ext
  funext A
  apply hom_ext R S B A
  intro x y
  change (coefficientMap R S (𝟙 B : B ⟶ B) A).hom (pairing R S B A x y) =
    pairing R S B A x y
  rw [coefficientMap_pairing]
  rfl

/-- For bimodule morphisms f:B→B′ and g:B′→B″,
the coefficient transformation of g∘f equals the
transformation of f followed by that of g. -/
theorem coefficientTransformation_comp (f : B ⟶ B') (g : B' ⟶ B'') :
    coefficientTransformation R S f ≫ coefficientTransformation R S g =
      coefficientTransformation R S (f ≫ g) := by
  apply NatTrans.ext
  funext A
  apply hom_ext R S B A
  intro x y
  change (coefficientMap R S g A).hom
      ((coefficientMap R S f A).hom (pairing R S B A x y)) =
    (coefficientMap R S (f ≫ g) A).hom (pairing R S B A x y)
  rw [coefficientMap_pairing, coefficientMap_pairing, coefficientMap_pairing]
  rfl

/-- For bimodule morphisms f,g:B→B′, the natural
transformation for f+g is the sum of those for f and g.
This is additivity in the coefficient Hom group. -/
theorem coefficientTransformation_add (f g : B ⟶ B') :
    coefficientTransformation R S (f + g) =
      coefficientTransformation R S f + coefficientTransformation R S g := by
  apply NatTrans.ext
  funext A
  apply hom_ext R S B A
  intro x y
  change (coefficientMap R S (f + g) A).hom (pairing R S B A x y) =
    ((coefficientMap R S f A).hom + (coefficientMap R S g A).hom)
      (pairing R S B A x y)
  rw [LinearMap.add_apply, coefficientMap_pairing, coefficientMap_pairing,
    coefficientMap_pairing, ModuleCat.hom_add, LinearMap.add_apply]
  exact (pairing R S B' A x).map_add (f.hom y) (g.hom y)

end Coefficients

/-- The category ModuleCat^b(E_(R,S)) maps to the functor
category from right R-modules in world a to right S-modules
in world max(a,b), by B↦−⊗_R B.
Its morphisms are the coefficient transformations. -/
def functorFactory :
    ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ) ⥤
      (ModuleCat.{a} Rᵐᵒᵖ ⥤ ModuleCat.{max a b} Sᵐᵒᵖ) where
  obj := functor R S
  map := coefficientTransformation R S
  map_id _ := coefficientTransformation_id R S
  map_comp f g := (coefficientTransformation_comp R S f g).symm

/-- The functor B↦−⊗_R B from E_(R,S)-modules to
right-module tensor functors preserves addition of
bimodule morphisms. -/
instance functorFactory_additive : (functorFactory R S).Additive where
  map_add {B B' f g} := coefficientTransformation_add R S f g

section ScalarChange

variable {R' : Type r'} {S' : Type s'} [Ring R'] [Ring S']
  (φ : R →+* R') (ψ : S →+* S')
  (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ))
  (B' : ModuleCat.{b} (R' ⊗[ℤ] S'ᵐᵒᵖ))
  (f : B ⟶ (RingChange.restrictFunctor φ ψ).obj B')

/-- For φ:R→R′, ψ:S→S′ and f:B→Res_(φ,ψ)(B′),
the map on a right R′-module A′ is
Res_(φᵒᵖ)(A′)⊗_R B→Res_(ψᵒᵖ)(A′⊗_(R′)B′).
It applies f to B and leaves the underlying input A′ fixed. -/
def ringChangeMap (A : ModuleCat.{a} R'ᵐᵒᵖ) :
    obj R S B ((ModuleCat.restrictScalars φ.op).obj A) ⟶
      (ModuleCat.restrictScalars ψ.op).obj (obj R' S' B' A) := by
  let X := (ModuleCat.restrictScalars φ.op).obj A
  letI := RingChange.leftModule R S B
  letI := RingChange.rightModule R S B
  letI := RingChange.commute R S B
  letI := RingChange.leftModule R' S' B'
  letI := RingChange.rightModule R' S' B'
  letI := RingChange.commute R' S' B'
  letI := TensorProduct.Balanced.rightModule ℤ R S X B
  letI := TensorProduct.Balanced.rightModule ℤ R' S' A B'
  let fE : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B' :=
    (ModuleCat.semilinearMapAddEquiv (RingChange.envelopingRingHom φ ψ) B B').symm f
  let f₀ : B →ₗ[ℤ] B' := fE.toAddMonoidHom.toIntLinearMap
  let x₀ : X →ₗ[ℤ] A :=
    (show X →+ A from { toFun := id, map_zero' := rfl, map_add' := fun _ _ => rfl }).toIntLinearMap
  have hx : ∀ (r : R) (x : X), x₀ (op r • x) = op (φ r) • x₀ x := by
    intro r x
    rfl
  have hL : ∀ (r : R) (y : B), f₀ (r • y) = φ r • f₀ y :=
    RingChange.map_left_smul φ ψ B B' fE
  have hR : ∀ (t : Sᵐᵒᵖ) (y : B), f₀ (t • y) = ψ.op t • f₀ y :=
    RingChange.map_right_smul φ ψ B B' fE
  let h : (obj R S B X).carrier →ₛₗ[ψ.op] (obj R' S' B' A).carrier :=
    TensorProduct.Balanced.mapSemilinearRight φ ψ.op x₀ f₀ hx hL hR
  exact ModuleCat.semilinearMapAddEquiv ψ.op (obj R S B X) (obj R' S' B' A) h

/-- For endpoint ring maps φ,ψ and the restricted bimodule
map f, the tensor ring-change map has value
[x⊗y]↦[x⊗f(y)].
The target class is balanced over R′ and viewed as a right S-module
through ψᵒᵖ. -/
theorem ringChangeMap_pairing (A : ModuleCat.{a} R'ᵐᵒᵖ) (x : A) (y : B) :
    (ringChangeMap R S φ ψ B B' f A).hom
        (pairing R S B ((ModuleCat.restrictScalars φ.op).obj A) x y) =
      pairing R' S' B' A x (f.hom y) := rfl

/-- For φ:R→R′, ψ:S→S′ and f:B→Res_(φ,ψ)(B′),
the maps Res_(φᵒᵖ)(A′)⊗_R B→Res_(ψᵒᵖ)(A′⊗_(R′)B′)
form a natural transformation in A′.
The rings need not be commutative. -/
def ringChangeTransformation :
    ModuleCat.restrictScalars φ.op ⋙ functor R S B ⟶
      functor R' S' B' ⋙ ModuleCat.restrictScalars ψ.op where
  app := ringChangeMap R S φ ψ B B' f
  naturality {A A'} g := by
    apply hom_ext R S B ((ModuleCat.restrictScalars φ.op).obj A)
    intro x y
    change (ringChangeMap R S φ ψ B B' f A').hom
      ((map R S B ((ModuleCat.restrictScalars φ.op).map g)).hom
        (pairing R S B ((ModuleCat.restrictScalars φ.op).obj A) x y)) =
      ((ModuleCat.restrictScalars ψ.op).map (map R' S' B' g)).hom
        ((ringChangeMap R S φ ψ B B' f A).hom
          (pairing R S B ((ModuleCat.restrictScalars φ.op).obj A) x y))
    change pairing R' S' B' A' (g.hom (show A from x)) (f.hom y) =
      (map R' S' B' g).hom (pairing R' S' B' A (show A from x) (f.hom y))
    exact (map_pairing R' S' B' g (show A from x) (f.hom y)).symm

/-- For f:B→Res(B′) and a target bimodule map g:B′→B″,
changing rings by f then applying g on the target coefficient
equals the ring-change transformation for the composite
B→Res(B″). -/
theorem ringChangeTransformation_coefficient_right
    {B'' : ModuleCat.{b} (R' ⊗[ℤ] S'ᵐᵒᵖ)} (g : B' ⟶ B'') :
    ringChangeTransformation R S φ ψ B B' f ≫
        Functor.whiskerRight (coefficientTransformation R' S' g)
          (ModuleCat.restrictScalars ψ.op) =
      ringChangeTransformation R S φ ψ B B''
        (f ≫ (RingChange.restrictFunctor φ ψ).map g) := by
  apply NatTrans.ext
  funext A
  apply hom_ext R S B ((ModuleCat.restrictScalars φ.op).obj A)
  intro x y
  change (coefficientMap R' S' g A).hom
      ((ringChangeMap R S φ ψ B B' f A).hom
        (pairing R S B ((ModuleCat.restrictScalars φ.op).obj A) x y)) =
    (ringChangeMap R S φ ψ B B''
      (f ≫ (RingChange.restrictFunctor φ ψ).map g) A).hom
        (pairing R S B ((ModuleCat.restrictScalars φ.op).obj A) x y)
  change (coefficientMap R' S' g A).hom
      (pairing R' S' B' A (show A from x) (f.hom y)) =
    pairing R' S' B'' A (show A from x) (g.hom (f.hom y))
  exact coefficientMap_pairing R' S' g A (show A from x) (f.hom y)

/-- For a source bimodule map g:B₀→B and ring-change
coefficient map f:B→Res(B′), applying g first then changing
rings equals the ring-change transformation for f∘g. -/
theorem ringChangeTransformation_coefficient_left
    {B₀ : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ)} (g : B₀ ⟶ B) :
    Functor.whiskerLeft (ModuleCat.restrictScalars φ.op)
        (coefficientTransformation R S g) ≫
      ringChangeTransformation R S φ ψ B B' f =
    ringChangeTransformation R S φ ψ B₀ B' (g ≫ f) := by
  apply NatTrans.ext
  funext A
  apply hom_ext R S B₀ ((ModuleCat.restrictScalars φ.op).obj A)
  intro x y
  change (ringChangeMap R S φ ψ B B' f A).hom
      ((coefficientMap R S g ((ModuleCat.restrictScalars φ.op).obj A)).hom
        (pairing R S B₀ ((ModuleCat.restrictScalars φ.op).obj A) x y)) =
    (ringChangeMap R S φ ψ B₀ B' (g ≫ f) A).hom
      (pairing R S B₀ ((ModuleCat.restrictScalars φ.op).obj A) x y)
  have h := coefficientMap_pairing R S g
    ((ModuleCat.restrictScalars φ.op).obj A) x y
  have h' := congrArg (ringChangeMap R S φ ψ B B' f A).hom h
  change (ringChangeMap R S φ ψ B B' f A).hom
      ((coefficientMap R S g ((ModuleCat.restrictScalars φ.op).obj A)).hom
        (pairing R S B₀ ((ModuleCat.restrictScalars φ.op).obj A) x y)) =
    (ringChangeMap R S φ ψ B B' f A).hom
      (pairing R S B ((ModuleCat.restrictScalars φ.op).obj A) x (g.hom y))
  exact h'

end ScalarChange

section Coherence

variable (B : ModuleCat.{b} (R ⊗[ℤ] Sᵐᵒᵖ))

/-- For identity endpoint ring maps and the identity bimodule
coefficient, the tensor ring-change map identifies with id
on A⊗_R B after the canonical input and output restriction
identity isomorphisms. Its pure value is [x⊗y]. -/
theorem ringChangeMap_id (A : ModuleCat.{a} Rᵐᵒᵖ) :
    ringChangeMap R S (RingHom.id R) (RingHom.id S) B B
        ((RingChange.restrictId (R := R) (S := S)).inv.app B) A =
      map R S B
          ((ModuleCat.restrictScalarsId' (RingHom.id R).op (by ext t; rfl)).hom.app A) ≫
        ((ModuleCat.restrictScalarsId' (RingHom.id S).op (by ext t; rfl)).inv.app
          (obj R S B A)) := by
  apply hom_ext R S B ((ModuleCat.restrictScalars (RingHom.id R).op).obj A)
  intro x y
  rfl

variable {R' : Type r'} {S' : Type s'} [Ring R'] [Ring S']
  {R'' : Type r''} {S'' : Type s''} [Ring R''] [Ring S'']
  (φ : R →+* R') (ψ : S →+* S') (φ' : R' →+* R'') (ψ' : S' →+* S'')
  (B' : ModuleCat.{b} (R' ⊗[ℤ] S'ᵐᵒᵖ))
  (B'' : ModuleCat.{b} (R'' ⊗[ℤ] S''ᵐᵒᵖ))
  (f : B ⟶ (RingChange.restrictFunctor φ ψ).obj B')
  (g : B' ⟶ (RingChange.restrictFunctor φ' ψ').obj B'')

/-- For composable endpoint ring maps and compatible
coefficient maps f:B→B′ and g:B′→B″, the two tensor changes
compose to the change for g∘f.
The equality uses the canonical input, coefficient and output
restriction-composition comparisons, and preserves [x⊗g(f(y))]. -/
theorem ringChangeMap_comp (A : ModuleCat.{a} R''ᵐᵒᵖ) :
    let eA := ModuleCat.restrictScalarsComp' φ.op φ'.op (φ'.comp φ).op (by ext t; rfl)
    let eS := ModuleCat.restrictScalarsComp' ψ.op ψ'.op (ψ'.comp ψ).op (by ext t; rfl)
    let fg : B ⟶ (RingChange.restrictFunctor (φ'.comp φ) (ψ'.comp ψ)).obj B'' :=
      f ≫ (RingChange.restrictFunctor φ ψ).map g ≫
        (RingChange.restrictComp φ ψ φ' ψ').inv.app B''
    map R S B (eA.hom.app A) ≫
        ringChangeMap R S φ ψ B B' f ((ModuleCat.restrictScalars φ'.op).obj A) ≫
        (ModuleCat.restrictScalars ψ.op).map (ringChangeMap R' S' φ' ψ' B' B'' g A) ≫
        eS.inv.app (obj R'' S'' B'' A) =
      ringChangeMap R S (φ'.comp φ) (ψ'.comp ψ) B B'' fg A := by
  dsimp only
  apply hom_ext R S B ((ModuleCat.restrictScalars (φ'.comp φ).op).obj A)
  intro x y
  rfl

end Coherence

end ModuleCat.Bimodule.Tensor
