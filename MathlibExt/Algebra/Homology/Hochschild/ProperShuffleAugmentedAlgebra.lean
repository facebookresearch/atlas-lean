/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleCotangentNaturality
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Proper-shuffle cotangent diagrams of augmented algebras

Let k be a commutative ring, B a commutative k-algebra and M a B-module whose
ground action is compatible with its B-action. Every algebra augmented to B acts
on M through its augmentation. Proper-shuffle cotangent complexes and coefficient
Kähler-differential modules define functors on the category of algebras over B.

The quotient maps send a coefficient tensor word to the word obtained by applying
the algebra map, with its coefficient unchanged. Their cotangent augmentations
form a natural transformation to the complexes concentrated in degree zero on
the coefficient cotangent modules.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra

variable (k : Type u) [CommRing k] (B : CommAlgCat.{max u v} k)
  (M : Type w) [AddCommGroup M] [Module k M] [Module B M]
  [SMulCommClass k B M] [IsScalarTower k B M]

/-- Let k be commutative, B a commutative k-algebra and M a B-module. An augmented algebra ε_P : A_P
→ B gives M the A_P-module action a·m=ε_P(a)·m, by restriction along the augmentation. -/
local instance coefficientModule (P : Over B) : Module P.left M :=
  Module.compHom M P.hom.hom.toRingHom

/-- Let k be commutative, B a commutative k-algebra and M both a k-module and a B-module whose
actions commute. For ε_P : A_P → B, the pulled-back A_P-action also commutes with k:
r·(a·m)=a·(r·m), since a acts as ε_P(a). -/
local instance coefficientCommutes (P : Over B) : SMulCommClass k P.left M where
  smul_comm r p m := by
    change r • (P.hom.hom p • m) = P.hom.hom p • (r • m)
    exact smul_comm r (P.hom.hom p) m

/-- Let k be commutative, B a commutative k-algebra and M a k/B-module with the scalar-tower
identity. Pulling the B-action back through ε_P : A_P → B gives (r·a)·m=r·(a·m), so k,A_P,M form
a scalar tower. -/
local instance coefficientTower (P : Over B) : IsScalarTower k P.left M where
  smul_assoc r p m := by
    change P.hom.hom (r • p) • m = r • (P.hom.hom p • m)
    exact (congrArg (fun b : B => b • m) (P.hom.hom.toLinearMap.map_smul r p)).trans
      (smul_assoc r (P.hom.hom p) m)

omit [SMulCommClass k B M] [IsScalarTower k B M] in
/-- Let k be commutative, B a commutative k-algebra and M both a k-module and a B-module. For f : P
→ Q in Over(B), the identity of M intertwines the pulled-back actions: id_M(a·m)=f(a)·id_M(m),
because ε_Q∘f=ε_P. -/
theorem coefficientCompatibility {P Q : Over B} (f : P ⟶ Q) :
    ∀ p : P.left, ∀ m : M, (LinearMap.id : M →ₗ[k] M) (p • m) =
      f.left.hom p • (LinearMap.id : M →ₗ[k] M) m := by
  intro p m
  change P.hom.hom p • m = Q.hom.hom (f.left.hom p) • m
  exact congrArg (fun b : B => b • m) (ConcreteCategory.congr_hom f.w p).symm

/-- Let k be commutative, B a commutative k-algebra and M a B-module with its induced k-action. For
an augmented algebra P=(A_P,ε_P : A_P → B) in Over(B), complex(P) is the degree-shifted proper
quotient for A_P with coefficient M acted on through ε_P. Its degree-n term is the
proper-shuffle quotient in Hochschild degree n+1. -/
def complex (P : Over B) : ChainComplex (ModuleCat.{max u v w} k) ℕ := properCotangentComplex k P.left M

/-- Let k be commutative, B a commutative k-algebra and M a B-module with its induced k-action. For
an augmented algebra P=(A_P,ε_P : A_P → B) in Over(B), a map f : P → Q over B induces map(f)
between their proper-shuffle cotangent complexes. The coefficient map is id_M; in degree n its
representatives are sent by id_M⊗f^{⊗(n+1)}. -/
def map {P Q : Over B} (f : P ⟶ Q) : complex k B M P ⟶ complex k B M Q :=
  cotangentChainMap k f.left.hom (LinearMap.id : M →ₗ[k] M) (coefficientCompatibility k B M f)

/-- Let k be commutative, B a commutative k-algebra and M a B-module with induced k-action. The
assignment P ↦ properCotangentComplex(A_P,M), with A_P acting via its augmentation to B, defines
a functor Over(B) → ChainComplex(ModuleCat k,ℕ). Morphisms apply their algebra maps to tensor
tails and leave M fixed. -/
def functor : Over B ⥤ ChainComplex (ModuleCat.{max u v w} k) ℕ where
  obj := complex k B M
  map := map k B M
  map_id P := by
    change HomologicalComplex.restrictionMap
        (chainMap k (AlgHom.id k P.left) (LinearMap.id : M →ₗ[k] M) _) ComplexShape.positiveNatEmbedding =
      𝟙 ((positiveQuotient k P.left M).restriction ComplexShape.positiveNatEmbedding)
    exact (congrArg (fun t : positiveQuotient k P.left M ⟶ positiveQuotient k P.left M =>
      HomologicalComplex.restrictionMap t ComplexShape.positiveNatEmbedding) (chainMap_id k)).trans
        (HomologicalComplex.restrictionMap_id (K := positiveQuotient k P.left M) ComplexShape.positiveNatEmbedding)
  map_comp {P Q S} f g := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change quotientLinearMap k (g.left.hom.comp f.left.hom) (LinearMap.id : M →ₗ[k] M) (n + 1) =
      (quotientLinearMap k g.left.hom (LinearMap.id : M →ₗ[k] M) (n + 1)).comp
        (quotientLinearMap k f.left.hom (LinearMap.id : M →ₗ[k] M) (n + 1))
    exact (by
      simpa only [LinearMap.id_comp] using
        (quotientLinearMap_comp k f.left.hom g.left.hom (LinearMap.id : M →ₗ[k] M)
          (LinearMap.id : M →ₗ[k] M) (n + 1)).symm)

/-- Let k be commutative, B a commutative k-algebra and M a B-module with its induced k-action. For
an augmented algebra P=(A_P,ε_P : A_P → B) in Over(B), for f : P → Q, n ∈ ℕ and x ∈
M⊗_kA_P^{⊗(n+1)}, map(f)_n sends the class of x to the class of (id_M⊗f^{⊗(n+1)})(x) in the
proper quotient for A_Q. -/
theorem map_mkQ {P Q : Over B} (f : P ⟶ Q) (n : ℕ)
    (x : M ⊗[k] TensorPower k (n + 1) P.left) :
    ((map k B M f).f n).hom ((rawPositiveRelations k P.left M (n + 1)).mkQ x) =
      (rawPositiveRelations k Q.left M (n + 1)).mkQ
        (ModuleCat.Algebra.Hochschild.linearMap f.left.hom.toNonUnitalAlgHom LinearMap.id (n + 1) x) :=
  quotientLinearMap_mkQ k f.left.hom (LinearMap.id : M →ₗ[k] M) (n + 1) x

/-- Let k be commutative, B a commutative k-algebra and M a B-module with its induced k-action. For
an augmented algebra P=(A_P,ε_P : A_P → B) in Over(B), cotangentModule(P) is M⊗_{A_P}Ω_{A_P/k},
as a ground-ring module through the canonical coefficient one-form identification. -/
def cotangentModule (P : Over B) : (ModuleCat.{max u v w} k) := coefficientCotangentModule k P.left M

/-- Let k be commutative, B a commutative k-algebra and M a B-module with its induced k-action. For
an augmented algebra P=(A_P,ε_P : A_P → B) in Over(B), a morphism f : P → Q induces
cotangentMap(f) : M⊗_{A_P}Ω_{A_P/k} → M⊗_{A_Q}Ω_{A_Q/k}. Its differential-word formula is m⊗da ↦
m⊗d(f(a)). -/
def cotangentMap {P Q : Over B} (f : P ⟶ Q) : cotangentModule k B M P ⟶ cotangentModule k B M Q :=
  cotangentModuleMap k f.left.hom (LinearMap.id : M →ₗ[k] M) (coefficientCompatibility k B M f)

/-- Let k be commutative, B a commutative k-algebra and M a B-module with its induced k-action. For
an augmented algebra P=(A_P,ε_P : A_P → B) in Over(B), the degree-zero scalar augmentation
complex(P)₀ → M⊗_{A_P}Ω_{A_P/k} sends the degree-one coefficient tensor m⊗a to m⊗da, through the
quotient and one-form identifications. -/
def scalarAugmentation (P : Over B) : (complex k B M P).X 0 ⟶ cotangentModule k B M P :=
  properCotangentScalarAugmentation k P.left M

/-- Let k be commutative, B a commutative k-algebra and M a B-module with its induced k-action. For
an augmented algebra P=(A_P,ε_P : A_P → B) in Over(B), the scalar augmentation complex(P)₀ →
M⊗_{A_P}Ω_{A_P/k} is an epimorphism. Universal differentials da generate the Kähler module and
every coefficient tensor m⊗da is in its image. -/
local instance scalarAugmentation_epi (P : Over B) : Epi (scalarAugmentation k B M P) :=
  (ModuleCat.epi_iff_surjective _).mpr (properCotangentScalarAugmentation_surjective k P.left M)

/-- Let k be commutative, B a commutative k-algebra and M a B-module with induced k-action. For f :
P → Q in Over(B), map(f)₀ ≫ scalarAugmentation(Q) = scalarAugmentation(P) ≫ cotangentMap(f). -/
@[reassoc]
theorem scalarAugmentation_naturality {P Q : Over B} (f : P ⟶ Q) :
    (map k B M f).f 0 ≫ scalarAugmentation k B M Q =
      scalarAugmentation k B M P ≫ cotangentMap k B M f :=
  RationalProperShuffle.scalarAugmentation_naturality k f.left.hom (LinearMap.id : M →ₗ[k] M)
    (coefficientCompatibility k B M f)

/-- Let k be commutative, B a commutative k-algebra and M a B-module with its induced k-action. For
an augmented algebra P=(A_P,ε_P : A_P → B) in Over(B), cotangentMap(id_P) is the identity of
M⊗_{A_P}Ω_{A_P/k}. -/
theorem cotangentMap_id (P : Over B) : cotangentMap k B M (𝟙 P) = 𝟙 (cotangentModule k B M P) := by
  apply (cancel_epi (scalarAugmentation k B M P)).mp
  let t : (complex k B M P).X 0 ⟶ (complex k B M P).X 0 := (map k B M (𝟙 P)).f 0
  have ht : t = 𝟙 ((complex k B M P).X 0) :=
    congrArg (fun q : complex k B M P ⟶ complex k B M P => q.f 0) ((functor k B M).map_id P)
  have h : t ≫ scalarAugmentation k B M P =
      scalarAugmentation k B M P ≫ cotangentMap k B M (𝟙 P) :=
    scalarAugmentation_naturality k B M (𝟙 P)
  exact h.symm.trans
    (((congrArg (fun q : (complex k B M P).X 0 ⟶ (complex k B M P).X 0 =>
      q ≫ scalarAugmentation k B M P) ht).trans (Category.id_comp _)).trans (Category.comp_id _).symm)

/-- Let k be commutative, B a commutative k-algebra and M a B-module with induced k-action. For f :
P → Q and g : Q → S in Over(B), cotangentMap(gf)=cotangentMap(f) ≫ cotangentMap(g). -/
theorem cotangentMap_comp {P Q S : Over B} (f : P ⟶ Q) (g : Q ⟶ S) :
    cotangentMap k B M (f ≫ g) = cotangentMap k B M f ≫ cotangentMap k B M g := by
  apply (cancel_epi (scalarAugmentation k B M P)).mp
  let tf : (complex k B M P).X 0 ⟶ (complex k B M Q).X 0 := (map k B M f).f 0
  let tg : (complex k B M Q).X 0 ⟶ (complex k B M S).X 0 := (map k B M g).f 0
  let tfg : (complex k B M P).X 0 ⟶ (complex k B M S).X 0 := (map k B M (f ≫ g)).f 0
  have hcomp : tfg = tf ≫ tg :=
    congrArg (fun t : complex k B M P ⟶ complex k B M S => t.f 0) ((functor k B M).map_comp f g)
  have hfg : tfg ≫ scalarAugmentation k B M S =
      scalarAugmentation k B M P ≫ cotangentMap k B M (f ≫ g) :=
    scalarAugmentation_naturality k B M (f ≫ g)
  have hf : tf ≫ scalarAugmentation k B M Q = scalarAugmentation k B M P ≫ cotangentMap k B M f :=
    scalarAugmentation_naturality k B M f
  have hg : tg ≫ scalarAugmentation k B M S = scalarAugmentation k B M Q ≫ cotangentMap k B M g :=
    scalarAugmentation_naturality k B M g
  exact hfg.symm.trans
    ((congrArg (fun t : (complex k B M P).X 0 ⟶ (complex k B M S).X 0 =>
      t ≫ scalarAugmentation k B M S) hcomp).trans
      ((Category.assoc tf tg (scalarAugmentation k B M S)).trans
        ((congrArg (fun t => tf ≫ t) hg).trans
          ((Category.assoc tf (scalarAugmentation k B M Q) (cotangentMap k B M g)).symm.trans
            ((congrArg (fun t => t ≫ cotangentMap k B M g) hf).trans
              (Category.assoc (scalarAugmentation k B M P) (cotangentMap k B M f) (cotangentMap k B M g)))))))

/-- Let k be commutative, B a commutative k-algebra and M a B-module with induced k-action. The
objects M⊗_{A_P}Ω_{A_P/k} and maps m⊗da ↦ m⊗d(f(a)) define the functor cotangentFunctor :
Over(B) → ModuleCat k. -/
def cotangentFunctor : Over B ⥤ (ModuleCat.{max u v w} k) where
  obj := cotangentModule k B M
  map := cotangentMap k B M
  map_id := cotangentMap_id k B M
  map_comp := cotangentMap_comp k B M

/-- Let k be commutative, B a commutative k-algebra and M a B-module with induced k-action. The
proper-shuffle cotangent augmentations form a natural transformation from the cotangent-complex
functor on Over(B) to the degree-zero single-complex functor applied to the coefficient
Kähler-module functor. -/
def augmentationNat : functor k B M ⟶ cotangentFunctor k B M ⋙ ChainComplex.single₀ (ModuleCat.{max u v w} k) where
  app P := properShuffleCotangentMap k P.left M
  naturality {P Q} (f : P ⟶ Q) := by
    change map k B M f ≫ properShuffleCotangentMap k Q.left M =
      properShuffleCotangentMap k P.left M ≫
        (ChainComplex.single₀ (ModuleCat.{max u v w} k)).map (cotangentMap k B M f)
    exact augmentation_naturality k f.left.hom (LinearMap.id : M →ₗ[k] M)
      (coefficientCompatibility k B M f)

/-- Let k be commutative, B a commutative k-algebra and M a B-module with its induced k-action. For
an augmented algebra P=(A_P,ε_P : A_P → B) in Over(B), the component augmentationNat(P) is
exactly the chain map properShuffleCotangentMap(A_P,M) from complex(P) to the degree-zero
complex on its coefficient cotangent module. -/
theorem augmentationNat_app (P : Over B) :
    (augmentationNat k B M).app P = properShuffleCotangentMap k P.left M := rfl

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra
