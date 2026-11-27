/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricNaturality
public import MathlibExt.AlgebraicTopology.SimplicialObject.HomOfComponents
public import MathlibExt.Algebra.Homology.TensorHomFunctoriality

/-!
# Naturality of symmetric bar maps and shuffle pairings

Let k be a commutative ring, A,B commutative k-algebras, and M,N compatible symmetric
coefficients. A unital k-algebra map g : A → B and a k-linear coefficient map f : M → N
satisfying f(a·m) = g(a)·f(m) induce a simplicial map of coefficient bars. The face identities
use the action compatibility; the degeneracy identities use g(1)=1. The coefficient modules and
lifted regular modules are placed in a common universe containing the separate source and target
algebra universes.

The bar map gives a Hochschild chain map with components f ⊗ g^{⊗n}. It commutes with raw bar
coordinates and with normalization. Naturality of the degreewise tensor diagonal and the
Eilenberg–Zilber shuffle map gives naturality of the symmetric shuffle pairing on tensor product
chain complexes. Postcomposing the pairing with target normalization gives the corresponding
normalized-target square.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory Opposite
open scoped TensorProduct Simplicial MonoidalCategory

universe u v v' z

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable {k : Type u} [CommRing k]
  {A : Type v} [CommRing A] [Algebra k A]
  {B : Type v'} [CommRing B] [Algebra k B]
  {M N : Type (max u v v' z)} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module B N]
  [IsScalarTower k A M] [IsScalarTower k B N]

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible coefficient modules
with symmetric right actions. Place the coefficients in a common universe T = max(u,v,v′,z),
where k,A,B lie in u,v,v′. Let g : A →ₐ[k] B be unital and f : M →ₗ[k] N. In simplicial degree n
: ℕ, use the bar tensor coordinate isomorphisms to define a k-module map whose tensor formula is
m ⊗ a₁ ⊗ … ⊗ aₙ ↦ f(m) ⊗ g(a₁) ⊗ … ⊗ g(aₙ). -/
def coefficientBarMapComponent (g : A →ₐ[k] B) (f : M →ₗ[k] N) (n : ℕ) :
    (coefficientBar.{u, v, max u v v' z} k A M).obj (op ⦋n⦌) ⟶
      (coefficientBar.{u, v', max u v v' z} k B N).obj (op ⦋n⦌) :=
  (coefficientBarObjIso.{u, v, max u v v' z} k A M n).hom ≫
    ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) ≫
      (coefficientBarObjIso.{u, v', max u v v' z} k B N n).inv

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible coefficient modules
with symmetric right actions. Place the coefficients in a common universe T = max(u,v,v′,z),
where k,A,B lie in u,v,v′. Let g : A →ₐ[k] B be unital and f : M →ₗ[k] N. Assume f(a·m) =
g(a)·f(m). For n : ℕ and i ∈ Fin(n+2), the degree components cₙ satisfy cₙ₊₁ ≫ δᵢ^B = δᵢ^A ≫ cₙ.
Here δᵢ are the coefficient-bar faces, including both endpoint actions and the internal adjacent
multiplications. -/
theorem coefficientBarMapComponent_face (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) (i : Fin (n + 2)) :
    coefficientBarMapComponent.{u, v, v', z} g f (n + 1) ≫ (coefficientBar.{u, v', max u v v' z} k B N).δ i =
      (coefficientBar.{u, v, max u v v' z} k A M).δ i ≫ coefficientBarMapComponent.{u, v, v', z} g f n := by
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  let := opModule B N
  let := actionsComm B N
  let := kOpComm k B N
  let := kOpTower k B N
  have h : ModuleCat.ofHom
        (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f (n + 1)) ≫
      rawFace k B N n i = rawFace k A M n i ≫ ModuleCat.ofHom
        (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) :=
    ModuleCat.hom_ext (ModuleCat.Algebra.Hochschild.linearMap_face_comm
      g.toNonUnitalAlgHom f hf (rightAction_compatibility g.toNonUnitalAlgHom f hf) n i)
  apply (cancel_epi (coefficientBarObjIso.{u, v, max u v v' z} k A M (n + 1)).inv).1
  apply (cancel_mono (coefficientBarObjIso.{u, v', max u v v' z} k B N n).hom).1
  simpa only [coefficientBarMapComponent, rawFace, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

private theorem linearMap_degeneracy_comm (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (n : ℕ) (i : Fin (n + 1)) :
    letI := opModule A M
    letI := actionsComm A M
    letI := kOpComm k A M
    letI := kOpTower k A M
    letI := opModule B N
    letI := actionsComm B N
    letI := kOpComm k B N
    letI := kOpTower k B N
    (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f (n + 1)).comp
        (ModuleCat.Algebra.Hochschild.degeneracy k A M n i).hom =
      (ModuleCat.Algebra.Hochschild.degeneracy k B N n i).hom.comp
        (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) := by
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  let := opModule B N
  let := actionsComm B N
  let := kOpComm k B N
  let := kOpTower k B N
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [LinearMap.comp_apply]
  rw [ModuleCat.Algebra.Hochschild.degeneracy_tprod,
    ModuleCat.Algebra.Hochschild.linearMap_tprod,
    ModuleCat.Algebra.Hochschild.linearMap_tprod,
    ModuleCat.Algebra.Hochschild.degeneracy_tprod]
  apply congrArg (fun t : TensorPower k (n + 1) B => f m ⊗ₜ[k] t)
  apply congrArg (PiTensorProduct.tprod k)
  funext j
  change g (Fin.insertNth (α := fun _ : Fin (n + 1) => A) i (1 : A) a j) =
    Fin.insertNth (α := fun _ : Fin (n + 1) => B) i (1 : B)
      (fun l : Fin n => g (a l)) j
  refine Fin.succAboveCases i ?_ (fun l => ?_) j
  · simp only [Fin.insertNth_apply_same, map_one]
  · simp only [Fin.insertNth_apply_succAbove]

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible coefficient modules
with symmetric right actions. Place the coefficients in a common universe T = max(u,v,v′,z),
where k,A,B lie in u,v,v′. Let g : A →ₐ[k] B be unital and f : M →ₗ[k] N. For n : ℕ and i ∈
Fin(n+1), the degree components satisfy cₙ ≫ sᵢ^B = sᵢ^A ≫ cₙ₊₁. The degeneracies insert 1 into
the algebra tail, so unitality g(1)=1 proves this square without a coefficient action-law
premise. -/
theorem coefficientBarMapComponent_degeneracy (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (n : ℕ) (i : Fin (n + 1)) :
    coefficientBarMapComponent.{u, v, v', z} g f n ≫ (coefficientBar.{u, v', max u v v' z} k B N).σ i =
      (coefficientBar.{u, v, max u v v' z} k A M).σ i ≫ coefficientBarMapComponent.{u, v, v', z} g f (n + 1) := by
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  let := opModule B N
  let := actionsComm B N
  let := kOpComm k B N
  let := kOpTower k B N
  have h : ModuleCat.ofHom
        (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) ≫
      ModuleCat.Algebra.Hochschild.degeneracy k B N n i =
    ModuleCat.Algebra.Hochschild.degeneracy k A M n i ≫ ModuleCat.ofHom
      (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f (n + 1)) :=
    ModuleCat.hom_ext (linearMap_degeneracy_comm.{u, v, v', z} g f n i).symm
  apply (cancel_epi (coefficientBarObjIso.{u, v, max u v v' z} k A M n).inv).1
  apply (cancel_mono (coefficientBarObjIso.{u, v', max u v v' z} k B N (n + 1)).hom).1
  simpa only [coefficientBarMapComponent, ModuleCat.Algebra.Hochschild.degeneracy,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id, coefficientBar, coefficientBarObjIso] using h

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible coefficient modules
with symmetric right actions. Place the coefficients in a common universe T = max(u,v,v′,z),
where k,A,B lie in u,v,v′. Let g : A →ₐ[k] B be unital and f : M →ₗ[k] N. Assume f(a·m) =
g(a)·f(m). The components applying f to the coefficient and g to each algebra factor, together
with their face and degeneracy identities, give a morphism of simplicial k-module coefficient
bars. -/
def coefficientBarMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    coefficientBar.{u, v, max u v v' z} k A M ⟶ coefficientBar.{u, v', max u v v' z} k B N :=
  SimplicialObject.homOfComponents (coefficientBarMapComponent.{u, v, v', z} g f)
    (fun {n} i => coefficientBarMapComponent_face.{u, v, v', z} g f hf n i)
    (fun {n} i => coefficientBarMapComponent_degeneracy.{u, v, v', z} g f n i)

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible coefficient modules
with symmetric right actions. Place the coefficients in a common universe T = max(u,v,v′,z),
where k,A,B lie in u,v,v′. Let g : A →ₐ[k] B be unital and f : M →ₗ[k] N. Assume f(a·m) =
g(a)·f(m). The component of coefficientBarMap g f hf at the simplex [n] equals
coefficientBarMapComponent g f n, the map m ⊗ a₁ ⊗ … ⊗ aₙ ↦ f(m) ⊗ g(a₁) ⊗ … ⊗ g(aₙ) in bar
coordinates. -/
@[simp]
theorem coefficientBarMap_app_mk (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    (coefficientBarMap.{u, v, v', z} g f hf).app (op ⦋n⦌) = coefficientBarMapComponent.{u, v, v', z} g f n :=
  SimplicialObject.homOfComponents_app_mk (coefficientBarMapComponent.{u, v, v', z} g f)
    (fun {n} i => coefficientBarMapComponent_face.{u, v, v', z} g f hf n i)
    (fun {n} i => coefficientBarMapComponent_degeneracy.{u, v, v', z} g f n i) n

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible coefficient modules
with symmetric right actions. Place the coefficients in a common universe T = max(u,v,v′,z),
where k,A,B lie in u,v,v′. Let g : A →ₐ[k] B be unital and f : M →ₗ[k] N. Assume f(a·m) =
g(a)·f(m). Applying f to the coefficient and g to every algebra tail gives a chain map C(A,M) →
C(B,N) of ℕ-indexed Hochschild chain complexes. Symmetry supplies the right-action compatibility
from the stated left-action law. -/
def coefficientChainMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) : chainComplex k A M ⟶ chainComplex k B N := by
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  let := opModule B N
  let := actionsComm B N
  let := kOpComm k B N
  let := kOpTower k B N
  exact ModuleCat.Algebra.Hochschild.map.{u, v, v', z} g.toNonUnitalAlgHom f hf
    (rightAction_compatibility g.toNonUnitalAlgHom f hf)

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible coefficient modules
with symmetric right actions. Place the coefficients in a common universe T = max(u,v,v′,z),
where k,A,B lie in u,v,v′. Let g : A →ₐ[k] B be unital and f : M →ₗ[k] N. Assume f(a·m) =
g(a)·f(m). For n : ℕ, the nth component of coefficientChainMap is the k-linear tensor map f ⊗
g^{⊗n} : M ⊗_k A^{⊗n} → N ⊗_k B^{⊗n}. -/
@[simp]
theorem coefficientChainMap_f (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    (coefficientChainMap.{u, v, v', z} g f hf).f n =
      ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) := by
  rfl

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible coefficient modules
with symmetric right actions. Place the coefficients in a common universe T = max(u,v,v′,z),
where k,A,B lie in u,v,v′. Let g : A →ₐ[k] B be unital and f : M →ₗ[k] N. Assume f(a·m) =
g(a)·f(m). Let c_A,c_B identify raw Hochschild chains with the alternating-face complexes of
their coefficient bars, let b be coefficientBarMap and AF the alternating-face complex functor.
Then coefficientChainMap ≫ c_B.hom = c_A.hom ≫ AF(b). -/
@[reassoc]
theorem coefficientChainMap_comp_chainComplexIso (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    coefficientChainMap.{u, v, v', z} g f hf ≫ (chainComplexIso.{u, v', max u v v' z} k B N).hom =
      (chainComplexIso.{u, v, max u v v' z} k A M).hom ≫
        (AlgebraicTopology.alternatingFaceMapComplex _).map (coefficientBarMap.{u, v, v', z} g f hf) := by
  apply HomologicalComplex.hom_ext
  intro n
  change (coefficientChainMap.{u, v, v', z} g f hf).f n ≫ (coefficientBarObjIso.{u, v', max u v v' z} k B N n).inv =
    (coefficientBarObjIso.{u, v, max u v v' z} k A M n).inv ≫ (coefficientBarMap.{u, v, v', z} g f hf).app (op ⦋n⦌)
  rw [coefficientChainMap_f.{u, v, v', z}, coefficientBarMap_app_mk.{u, v, v', z}]
  change ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) ≫
      (coefficientBarObjIso.{u, v', max u v v' z} k B N n).inv =
    (coefficientBarObjIso.{u, v, max u v v' z} k A M n).inv ≫
      (coefficientBarObjIso.{u, v, max u v v' z} k A M n).hom ≫
        ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) ≫
          (coefficientBarObjIso.{u, v', max u v v' z} k B N n).inv
  exact ((coefficientBarObjIso.{u, v, max u v v' z} k A M n).inv_hom_id_assoc
    (ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) ≫
      (coefficientBarObjIso.{u, v', max u v v' z} k B N n).inv)).symm

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible coefficient modules
with symmetric right actions. Place the coefficients in a common universe T = max(u,v,v′,z),
where k,A,B lie in u,v,v′. Let g : A →ₐ[k] B be unital and f : M →ₗ[k] N. Assume f(a·m) =
g(a)·f(m). The simplicial coefficient bar map induces a map on the quotients by degeneracies.
Transporting through the normalized tensor coordinate isomorphisms defines
normalizedCoefficientMap : C̄(A,M) → C̄(B,N). -/
def normalizedCoefficientMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    normalizedChainComplex k A M ⟶ normalizedChainComplex k B N := by
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  let := opModule B N
  let := actionsComm B N
  let := kOpComm k B N
  let := kOpTower k B N
  exact (ModuleCat.Algebra.Hochschild.normalizationIso k A M).inv ≫
    AlgebraicTopology.NormalizedQuotient.map (coefficientBarMap.{u, v, v', z} g f hf) ≫
      (ModuleCat.Algebra.Hochschild.normalizationIso k B N).hom

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible coefficient modules
with symmetric right actions. Place the coefficients in a common universe T = max(u,v,v′,z),
where k,A,B lie in u,v,v′. Let g : A →ₐ[k] B be unital and f : M →ₗ[k] N. Assume f(a·m) =
g(a)·f(m). If π_A,π_B are the normalization projections, F = coefficientChainMap and F̄ =
normalizedCoefficientMap, then π_A ≫ F̄ = F ≫ π_B as chain maps. -/
@[reassoc]
theorem normalizationProjection_coefficientMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    normalizationProjection.{u, v, max u v v' z} k A M ≫ normalizedCoefficientMap.{u, v, v', z} g f hf =
      coefficientChainMap.{u, v, v', z} g f hf ≫ normalizationProjection.{u, v', max u v v' z} k B N := by
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  let := opModule B N
  let := actionsComm B N
  let := kOpComm k B N
  let := kOpTower k B N
  let F := AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v v' z} k)
  let X : SimplicialObject (ModuleCat.{max u v v' z} k) :=
    coefficientBar.{u, v, max u v v' z} k A M
  let Y : SimplicialObject (ModuleCat.{max u v v' z} k) :=
    coefficientBar.{u, v', max u v v' z} k B N
  let cA : chainComplex k A M ≅ F.obj X :=
    chainComplexIso.{u, v, max u v v' z} k A M
  let cB : chainComplex k B N ≅ F.obj Y :=
    chainComplexIso.{u, v', max u v v' z} k B N
  let eA : AlgebraicTopology.NormalizedQuotient.obj X ≅ normalizedChainComplex k A M :=
    ModuleCat.Algebra.Hochschild.normalizationIso.{u, v, max u v v' z} k A M
  let eB : AlgebraicTopology.NormalizedQuotient.obj Y ≅ normalizedChainComplex k B N :=
    ModuleCat.Algebra.Hochschild.normalizationIso.{u, v', max u v v' z} k B N
  let pA := AlgebraicTopology.NormalizedQuotient.projection X
  let pB := AlgebraicTopology.NormalizedQuotient.projection Y
  let b : X ⟶ Y := coefficientBarMap.{u, v, v', z} g f hf
  let q := AlgebraicTopology.NormalizedQuotient.map b
  have hνA : normalizationProjection.{u, v, max u v v' z} k A M = (cA.hom ≫ pA) ≫ eA.hom := by rfl
  have hνB : normalizationProjection.{u, v', max u v v' z} k B N = (cB.hom ≫ pB) ≫ eB.hom := by rfl
  have hq : normalizedCoefficientMap.{u, v, v', z} g f hf = eA.inv ≫ q ≫ eB.hom := by rfl
  have hp : pA ≫ q = F.map b ≫ pB :=
    AlgebraicTopology.NormalizedQuotient.projection_map b
  have hc : coefficientChainMap.{u, v, v', z} g f hf ≫ cB.hom = cA.hom ≫ F.map b :=
    coefficientChainMap_comp_chainComplexIso.{u, v, v', z} g f hf
  rw [hνA, hq, hνB]
  calc
    ((cA.hom ≫ pA) ≫ eA.hom) ≫ (eA.inv ≫ q ≫ eB.hom) =
        cA.hom ≫ (pA ≫ q) ≫ eB.hom := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = cA.hom ≫ (F.map b ≫ pB) ≫ eB.hom := by rw [hp]
    _ = (cA.hom ≫ F.map b) ≫ pB ≫ eB.hom := by simp only [Category.assoc]
    _ = (coefficientChainMap.{u, v, v', z} g f hf ≫ cB.hom) ≫ pB ≫ eB.hom := by rw [hc]
    _ = coefficientChainMap.{u, v, v', z} g f hf ≫ ((cB.hom ≫ pB) ≫ eB.hom) := by
      simp only [Category.assoc]

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible coefficient modules
with symmetric right actions. Place the coefficients in a common universe T = max(u,v,v′,z),
where k,A,B lie in u,v,v′. Let g : A →ₐ[k] B be unital and f : M →ₗ[k] N. Assume f(a·m) =
g(a)·f(m). Let b_R be the coefficient bar map for the lifted regular coefficient g and b_M the
map for f. With AF the alternating-face complex functor and Δ_A,Δ_B the diagonal maps from the
degreewise tensor of these bars to Hochschild chains, AF(b_R ⊗ b_M) ≫ Δ_B = Δ_A ≫
coefficientChainMap. -/
@[reassoc]
theorem diagonalChainMap_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  (AlgebraicTopology.alternatingFaceMapComplex _).map
      (coefficientBarMap.{u, v, v', z} g
        (regularCoefficientMap g.toNonUnitalAlgHom :
          ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B)
        (regularCoefficientMap_smul.{u, v, v', max u v v' z, max u v v' z}
          g.toNonUnitalAlgHom) ⊗ₘ coefficientBarMap.{u, v, v', z} g f hf) ≫
    diagonalChainMap.{u, v', max u v v' z} k B N =
  diagonalChainMap.{u, v, max u v v' z} k A M ≫ coefficientChainMap.{u, v, v', z} g f hf := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, coefficientChainMap_f.{u, v, v', z}]
  change ((coefficientBarMap.{u, v, v', z} g
      (regularCoefficientMap g.toNonUnitalAlgHom :
        ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B)
      (regularCoefficientMap_smul.{u, v, v', max u v v' z, max u v v' z}
          g.toNonUnitalAlgHom)).app (op ⦋n⦌) ⊗ₘ
      (coefficientBarMap.{u, v, v', z} g f hf).app (op ⦋n⦌)) ≫ diagonalComponent.{u, v', max u v v' z} k B N n =
    diagonalComponent.{u, v, max u v v' z} k A M n ≫ ModuleCat.ofHom
      (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n)
  have h :
      (ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom
        (regularCoefficientMap g.toNonUnitalAlgHom :
          ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B) n) ⊗ₘ
      ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n)) ≫
        ModuleCat.ofHom (diagonalRaw.{u, v', max u v v' z} k B N n) =
      ModuleCat.ofHom (diagonalRaw.{u, v, max u v v' z} k A M n) ≫ ModuleCat.ofHom
        (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) :=
    by
      apply ModuleCat.hom_ext
      change (diagonalRaw.{u, v', max u v v' z} k B N n).comp
          (TensorProduct.map
            (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom
              (regularCoefficientMap g.toNonUnitalAlgHom :
                ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B) n)
            (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n)) =
        (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n).comp
          (diagonalRaw.{u, v, max u v v' z} k A M n)
      exact (diagonalRaw_naturality g.toNonUnitalAlgHom f hf n).symm
  have paste
      {X₁ X₂ Y₁ Y₂ R₁ R₂ L₁ L₂ T T' : ModuleCat.{max u v v' z} k}
      (a : X₁ ≅ R₁) (b : X₂ ≅ R₂) (c : Y₁ ≅ L₁) (d : Y₂ ≅ L₂)
      (r : R₁ ⟶ L₁) (s : R₂ ⟶ L₂) (δ : R₁ ⊗ R₂ ⟶ T) (ε : L₁ ⊗ L₂ ⟶ T')
      (t : T ⟶ T') (hδ : (r ⊗ₘ s) ≫ ε = δ ≫ t) :
      ((a.hom ≫ r ≫ c.inv) ⊗ₘ (b.hom ≫ s ≫ d.inv)) ≫ ((c.hom ⊗ₘ d.hom) ≫ ε) =
        ((a.hom ⊗ₘ b.hom) ≫ δ) ≫ t := by
    calc
      _ = (((a.hom ≫ r ≫ c.inv) ≫ c.hom) ⊗ₘ
          ((b.hom ≫ s ≫ d.inv) ≫ d.hom)) ≫ ε := by
        rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
      _ = ((a.hom ≫ r) ⊗ₘ (b.hom ≫ s)) ≫ ε := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = (a.hom ⊗ₘ b.hom) ≫ ((r ⊗ₘ s) ≫ ε) := by
        rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
      _ = _ := by rw [hδ, Category.assoc]
  simp only [coefficientBarMap, SimplicialObject.homOfComponents_app_mk,
    coefficientBarMapComponent]
  exact paste
    (coefficientBarObjIso k A (ULift.{max u v v' z} A) n)
    (coefficientBarObjIso.{u, v, max u v v' z} k A M n)
    (coefficientBarObjIso k B (ULift.{max u v v' z} B) n)
    (coefficientBarObjIso.{u, v', max u v v' z} k B N n)
    (ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom
      (regularCoefficientMap g.toNonUnitalAlgHom :
        ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B) n))
    (ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n))
    (ModuleCat.ofHom (diagonalRaw.{u, v, max u v v' z} k A M n))
    (ModuleCat.ofHom (diagonalRaw.{u, v', max u v v' z} k B N n))
    (ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n)) h

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible coefficient modules
with symmetric right actions. Place the coefficients in a common universe T = max(u,v,v′,z),
where k,A,B lie in u,v,v′. Let g : A →ₐ[k] B be unital and f : M →ₗ[k] N. Assume f(a·m) =
g(a)·f(m). Let F_R be the chain map of lifted regular coefficients induced by g and F_M =
coefficientChainMap g f hf. For the symmetric shuffle pairings P_A and P_B from the tensor
product chain complexes, (F_R ⊗ F_M) ≫ P_B = P_A ≫ F_M. -/
@[reassoc]
theorem pairing_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  HomologicalComplex.tensorHom
      (coefficientChainMap.{u, v, v', z} g
        (regularCoefficientMap g.toNonUnitalAlgHom :
          ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B)
        (regularCoefficientMap_smul.{u, v, v', max u v v' z, max u v v' z}
          g.toNonUnitalAlgHom)) (coefficientChainMap.{u, v, v', z} g f hf) ≫
    pairing.{u, v', max u v v' z} k B N =
      pairing.{u, v, max u v v' z} k A M ≫ coefficientChainMap.{u, v, v', z} g f hf := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  let r : ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B :=
    regularCoefficientMap g.toNonUnitalAlgHom
  let hr := regularCoefficientMap_smul.{u, v, v', max u v v' z, max u v v' z}
          g.toNonUnitalAlgHom
  let fR := coefficientChainMap.{u, v, v', z} g r hr
  let fM := coefficientChainMap.{u, v, v', z} g f hf
  let bR := coefficientBarMap.{u, v, v', z} g r hr
  let bM := coefficientBarMap.{u, v, v', z} g f hf
  let F := AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v v' z} k)
  let cR := chainComplexIso.{u, v, max u v v' z} k A (ULift.{max u v v' z} A)
  let cM := chainComplexIso.{u, v, max u v v' z} k A M
  let dR := chainComplexIso.{u, v', max u v v' z} k B (ULift.{max u v v' z} B)
  let dM := chainComplexIso.{u, v', max u v v' z} k B N
  have hR : fR ≫ dR.hom = cR.hom ≫ F.map bR :=
    coefficientChainMap_comp_chainComplexIso.{u, v, v', z} g r hr
  have hM : fM ≫ dM.hom = cM.hom ≫ F.map bM :=
    coefficientChainMap_comp_chainComplexIso.{u, v, v', z} g f hf
  have hShuffle : HomologicalComplex.tensorHom (F.map bR) (F.map bM) ≫
      AlgebraicTopology.EilenbergZilber.alternatingPairing
        (coefficientBar.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
          (coefficientBar.{u, v', max u v v' z} k B N) =
    AlgebraicTopology.EilenbergZilber.alternatingPairing
      (coefficientBar.{u, v, max u v v' z} k A (ULift.{max u v v' z} A)) (coefficientBar.{u, v, max u v v' z} k A M) ≫
        F.map (bR ⊗ₘ bM) :=
    AlgebraicTopology.EilenbergZilber.alternatingPairing_naturality bR bM
  have hDiagonal : F.map (bR ⊗ₘ bM) ≫ diagonalChainMap.{u, v', max u v v' z} k B N =
      diagonalChainMap.{u, v, max u v v' z} k A M ≫ fM := diagonalChainMap_naturality.{u, v, v', z} g f hf
  change HomologicalComplex.tensorHom fR fM ≫
      (HomologicalComplex.tensorHom dR.hom dM.hom ≫
        AlgebraicTopology.EilenbergZilber.alternatingPairing
          (coefficientBar.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
            (coefficientBar.{u, v', max u v v' z} k B N) ≫
            diagonalChainMap.{u, v', max u v v' z} k B N) =
    (HomologicalComplex.tensorHom cR.hom cM.hom ≫
      AlgebraicTopology.EilenbergZilber.alternatingPairing
        (coefficientBar.{u, v, max u v v' z} k A (ULift.{max u v v' z} A)) (coefficientBar.{u, v, max u v v' z} k A M) ≫
          diagonalChainMap.{u, v, max u v v' z} k A M) ≫ fM
  calc
    _ = (HomologicalComplex.tensorHom fR fM ≫
        HomologicalComplex.tensorHom dR.hom dM.hom) ≫
        AlgebraicTopology.EilenbergZilber.alternatingPairing
          (coefficientBar.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
            (coefficientBar.{u, v', max u v v' z} k B N) ≫
            diagonalChainMap.{u, v', max u v v' z} k B N := by simp only [Category.assoc]
    _ = HomologicalComplex.tensorHom (fR ≫ dR.hom) (fM ≫ dM.hom) ≫
        AlgebraicTopology.EilenbergZilber.alternatingPairing
          (coefficientBar.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
            (coefficientBar.{u, v', max u v v' z} k B N) ≫
            diagonalChainMap.{u, v', max u v v' z} k B N := by rw [HomologicalComplex.tensorHom_comp_tensorHom]
    _ = HomologicalComplex.tensorHom (cR.hom ≫ F.map bR) (cM.hom ≫ F.map bM) ≫
        AlgebraicTopology.EilenbergZilber.alternatingPairing
          (coefficientBar.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
            (coefficientBar.{u, v', max u v v' z} k B N) ≫
            diagonalChainMap.{u, v', max u v v' z} k B N := by rw [hR, hM]
    _ = HomologicalComplex.tensorHom cR.hom cM.hom ≫
        (HomologicalComplex.tensorHom (F.map bR) (F.map bM) ≫
          AlgebraicTopology.EilenbergZilber.alternatingPairing
            (coefficientBar.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
              (coefficientBar.{u, v', max u v v' z} k B N)) ≫
          diagonalChainMap.{u, v', max u v v' z} k B N := by
            rw [← HomologicalComplex.tensorHom_comp_tensorHom]
            simp only [Category.assoc]
    _ = HomologicalComplex.tensorHom cR.hom cM.hom ≫
        (AlgebraicTopology.EilenbergZilber.alternatingPairing
          (coefficientBar.{u, v, max u v v' z} k A (ULift.{max u v v' z} A))
            (coefficientBar.{u, v, max u v v' z} k A M) ≫
            F.map (bR ⊗ₘ bM)) ≫ diagonalChainMap.{u, v', max u v v' z} k B N := by rw [hShuffle]
    _ = HomologicalComplex.tensorHom cR.hom cM.hom ≫
        AlgebraicTopology.EilenbergZilber.alternatingPairing
          (coefficientBar.{u, v, max u v v' z} k A (ULift.{max u v v' z} A))
            (coefficientBar.{u, v, max u v v' z} k A M) ≫
            (F.map (bR ⊗ₘ bM) ≫ diagonalChainMap.{u, v', max u v v' z} k B N) := by simp only [Category.assoc]
    _ = _ := by rw [hDiagonal]; simp only [Category.assoc]

/-- Let k be a commutative ring, A,B commutative k-algebras and M,N compatible coefficient modules
with symmetric right actions. Place the coefficients in a common universe T = max(u,v,v′,z),
where k,A,B lie in u,v,v′. Let g : A →ₐ[k] B be unital and f : M →ₗ[k] N. Assume f(a·m) =
g(a)·f(m). Let F_R and F_M be the regular and coefficient chain maps, P_A,P_B the shuffle
pairings and π_A,π_B normalization. Then (F_R ⊗ F_M) ≫ (P_B ≫ π_B) = (P_A ≫ π_A) ≫
normalizedCoefficientMap. The inputs remain raw chain complexes and the pairing is normalized in
its target. -/
@[reassoc]
theorem pairing_normalizationProjection_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  HomologicalComplex.tensorHom
      (coefficientChainMap.{u, v, v', z} g
        (regularCoefficientMap g.toNonUnitalAlgHom :
          ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B)
        (regularCoefficientMap_smul.{u, v, v', max u v v' z, max u v v' z}
          g.toNonUnitalAlgHom)) (coefficientChainMap.{u, v, v', z} g f hf) ≫
    (pairing.{u, v', max u v v' z} k B N).postcomp
      (normalizationProjection.{u, v', max u v v' z} k B N) =
  (pairing.{u, v, max u v v' z} k A M).postcomp
      (normalizationProjection.{u, v, max u v v' z} k A M) ≫ normalizedCoefficientMap.{u, v, v', z} g f hf := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  rw [HomologicalComplex.ChainGradedPairing.postcomp,
    HomologicalComplex.ChainGradedPairing.postcomp, ← Category.assoc, pairing_naturality.{u, v, v', z}]
  rw [Category.assoc, ← normalizationProjection_coefficientMap.{u, v, v', z}]
  simp only [Category.assoc]

end ModuleCat.Algebra.Hochschild.Symmetric
