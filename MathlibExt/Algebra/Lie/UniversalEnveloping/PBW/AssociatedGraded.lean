/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.CompleteGradedCoordinates
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Polynomial coordinates on the graded enveloping quotient layers

Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L a basis indexed by a
linearly ordered type I. Write D_n for the degree filtration of U_R(L) and G_n=D_n/D_{<n}. The
direct sum ⊕_n G_n has PBW coordinates in MvPolynomial I R, carrying G_n to homogeneous
polynomials of degree n.

The resulting R-algebra structure has product symbol_n(u)·symbol_m(v)=symbol_{n+m}(uv), and
its scalar map is the degree-zero symbol. The homogeneous components are exactly the images of
the quotient layers and form a graded algebra with finite-support decomposition. No finiteness
of the basis index or characteristic condition is required.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped DirectSum

namespace UniversalEnvelopingAlgebra.PBW

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "P" => MvPolynomial I R

/-- Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L an ordered basis, with
LinearOrder I. Write G_n for the degree-n enveloping quotient D_n/D_{<n}. The associated
graded carrier attached to b consists of the finite-support direct sum ⊕_n G_n. The basis
parameter specifies its PBW polynomial coordinates; the quotient layers themselves come from
the degree filtration. -/
structure AssociatedGraded (b : Module.Basis I R L) where
  /-- For an ordered basis b : Basis I R L of an R-Lie algebra over a commutative ring R, an element
of the PBW associated graded carrier has quotient coordinates in GradedModule R L = ⊕_{n∈ℕ}
D_n/D_{<n}. The field toGradedModule is this finite-support direct-sum element, recording its
components in every degree. -/
  toGradedModule : GradedModule R L

/-- Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L with LinearOrder I. There
is a carrier equivalence between the PBW associated graded object attached to b and
GradedModule R L, the direct sum of the degree quotient layers. The forward map takes its
finite-support quotient coordinates, and the inverse forms the associated graded element with
those coordinates. -/
def associatedGradedRawEquiv (b : Module.Basis I R L) :
    AssociatedGraded b ≃ GradedModule R L where
  toFun := AssociatedGraded.toGradedModule
  invFun := AssociatedGraded.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L with LinearOrder I.
Combining the equivalence with the quotient-layer direct sum and the complete PBW
graded-module equivalence gives AssociatedGraded(b) ≃ MvPolynomial I R. Each degree-n quotient
component is sent to its homogeneous polynomial of degree n, and all degrees are combined
using finite support. -/
def associatedGradedCoordinateEquiv (b : Module.Basis I R L) : AssociatedGraded b ≃ P :=
  (associatedGradedRawEquiv b).trans (completeGradedModuleEquiv b).toEquiv

instance associatedGradedCommRing (b : Module.Basis I R L) : CommRing (AssociatedGraded b) :=
  (associatedGradedCoordinateEquiv b).commRing

instance associatedGradedAlgebra (b : Module.Basis I R L) : Algebra R (AssociatedGraded b) :=
  (associatedGradedCoordinateEquiv b).algebra R

/-- For a commutative ring R, an R-Lie algebra L, and an ordered basis b : Basis I R L, the
complete PBW coordinate bijection defines an R-algebra equivalence AssociatedGraded(b) ≃ₐ[R]
MvPolynomial I R. The operations on the associated graded carrier are transported through
these coordinates. The symbol multiplication theorem identifies this product with the class of
the enveloping product on homogeneous quotient layers. -/
def associatedGradedAlgEquiv (b : Module.Basis I R L) : AssociatedGraded b ≃ₐ[R] P :=
  (associatedGradedCoordinateEquiv b).algEquiv R

@[simp]
theorem associatedGradedAlgEquiv_apply (b : Module.Basis I R L) (x : AssociatedGraded b) :
    associatedGradedAlgEquiv b x = completeGradedModuleEquiv b x.toGradedModule := rfl

/-- Let b : Basis I R L be an ordered basis of an R-Lie algebra over a commutative ring R. For x,y
in AssociatedGraded(b), the finite-support quotient coordinates of x+y equal the sum of those
of x and y: (x+y).toGradedModule = x.toGradedModule + y.toGradedModule. Thus transported
polynomial addition agrees with the additive structure of the quotient-layer direct sum. -/
@[simp]
theorem associatedGraded_toGradedModule_add (b : Module.Basis I R L)
    (x y : AssociatedGraded b) : (x + y).toGradedModule = x.toGradedModule + y.toGradedModule := by
  apply (completeGradedModuleEquiv b).injective
  change associatedGradedAlgEquiv b (x + y) = _
  rw [map_add, map_add]
  rfl

/-- For an ordered basis b : Basis I R L of an R-Lie algebra over a commutative ring R, r ∈ R, and
x ∈ AssociatedGraded(b), one has (r·x).toGradedModule = r·x.toGradedModule. The scalar action
transported through the PBW polynomial coordinates therefore agrees with the R-module action
on the direct sum of enveloping degree quotients. -/
@[simp]
theorem associatedGraded_toGradedModule_smul (b : Module.Basis I R L)
    (r : R) (x : AssociatedGraded b) : (r • x).toGradedModule = r • x.toGradedModule := by
  apply (completeGradedModuleEquiv b).injective
  change associatedGradedAlgEquiv b (r • x) = _
  rw [map_smul, map_smul]
  rfl

/-- Let R be a commutative ring, L an R-Lie algebra, b : Basis I R L with LinearOrder I, and n ∈
ℕ. Define the R-linear map G_n → AssociatedGraded(b) by sending a quotient-layer element to
its homogeneous polynomial coordinate and then applying the inverse full polynomial coordinate
equivalence. Here G_n=D_n/D_{<n}; its image is the degree-n component of the associated graded
carrier. -/
def ofGradedLayer (b : Module.Basis I R L) (n : ℕ) : GradedLayer R L n →ₗ[R] AssociatedGraded b :=
  (associatedGradedAlgEquiv b).symm.toLinearMap.comp
    ((MvPolynomial.homogeneousSubmodule I R n).subtype.comp
      (completeGradedEquiv b n).toLinearMap)

theorem associatedGradedAlgEquiv_ofGradedLayer (b : Module.Basis I R L) (n : ℕ)
    (x : GradedLayer R L n) :
    associatedGradedAlgEquiv b (ofGradedLayer b n x) = (completeGradedEquiv b n x).val := by
  change associatedGradedAlgEquiv b
    ((associatedGradedAlgEquiv b).symm (completeGradedEquiv b n x).val) = _
  exact (associatedGradedAlgEquiv b).apply_symm_apply _

/-- Let b : Basis I R L be an ordered basis over a commutative ring R, n ∈ ℕ, and x ∈
G_n=D_n/D_{<n}. The quotient coordinates of ofGradedLayer(b,n,x) are DirectSum.lof at degree n
applied to x. Thus this associated graded element has coordinate x in degree n and zero
coordinates in all other degrees. -/
@[simp]
theorem ofGradedLayer_toGradedModule (b : Module.Basis I R L) (n : ℕ)
    (x : GradedLayer R L n) :
    (ofGradedLayer b n x).toGradedModule = DirectSum.lof R ℕ (GradedLayer R L) n x := by
  apply (completeGradedModuleEquiv b).injective
  change associatedGradedAlgEquiv b (ofGradedLayer b n x) = _
  rw [associatedGradedAlgEquiv_ofGradedLayer, completeGradedModuleEquiv_lof]

/-- For an ordered basis b : Basis I R L of an R-Lie algebra over a commutative ring R and n ∈ ℕ,
define symbol_n : D_n → AssociatedGraded(b) by quotienting by the lower stage D_{<n} and
embedding the resulting degree-n layer. At n=0 the lower stage is zero; for n>0 it is the
preceding degree stage inside D_n. -/
def symbol (b : Module.Basis I R L) (n : ℕ) :
    UniversalEnvelopingAlgebra.degreeFiltration R L n →ₗ[R] AssociatedGraded b :=
  (ofGradedLayer b n).comp (gradedLowerStage R L n).mkQ

theorem associatedGradedAlgEquiv_symbol (b : Module.Basis I R L) (n : ℕ)
    (u : UniversalEnvelopingAlgebra.degreeFiltration R L n) :
    associatedGradedAlgEquiv b (symbol b n u) =
      MvPolynomial.homogeneousComponent n (polynomialCoordinates b u.val) := by
  rw [symbol, LinearMap.comp_apply, associatedGradedAlgEquiv_ofGradedLayer,
    completeGradedEquiv_mk]
  rfl

/-- Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L with LinearOrder I. For
n,m ∈ ℕ, u ∈ D_n, and v ∈ D_m, one has symbol_n(u)·symbol_m(v) = symbol_{n+m}(uv). The product
uv is viewed in D_{n+m} using multiplicativity of the degree filtration. This identifies the
PBW coordinate product with the quotient symbol of the enveloping product for every pair of
degrees. -/
theorem symbol_mul (b : Module.Basis I R L) (n m : ℕ)
    (u : UniversalEnvelopingAlgebra.degreeFiltration R L n)
    (v : UniversalEnvelopingAlgebra.degreeFiltration R L m) :
    symbol b n u * symbol b m v =
      symbol b (n + m) ⟨u.val * v.val,
        UniversalEnvelopingAlgebra.mul_mem_degreeFiltration R L u.property v.property⟩ := by
  apply (associatedGradedAlgEquiv b).injective
  rw [map_mul, associatedGradedAlgEquiv_symbol, associatedGradedAlgEquiv_symbol,
    associatedGradedAlgEquiv_symbol]
  exact (homogeneous_polynomialCoordinates_mul b n m u.property v.property).symm

private theorem polynomialCoordinates_one (b : Module.Basis I R L) :
    polynomialCoordinates b (1 : U) = (1 : P) := by
  let xs : OrderedWord I := ⟨[], List.Pairwise.nil⟩
  have h := polynomialCoordinates_orderedWord b xs
  change polynomialCoordinates b (1 : U) = MvPolynomial.monomial (wordExponent []) 1 at h
  simpa only [wordExponent_nil, MvPolynomial.monomial_zero', MvPolynomial.C_1] using h

/-- For an ordered basis b : Basis I R L over a commutative ring R and r ∈ R, the degree-zero
symbol of algebraMap_R,U(r) equals algebraMap_R,AssociatedGraded(b)(r). The enveloping scalar
belongs to D_0, and its symbol is its class in the degree-zero quotient layer. Thus the
associated graded scalar map is the one induced by the enveloping scalar map. -/
theorem symbol_algebraMap (b : Module.Basis I R L) (r : R) :
    symbol b 0 ⟨algebraMap R U r,
      UniversalEnvelopingAlgebra.algebraMap_mem_degreeFiltration R L 0 r⟩ =
        algebraMap R (AssociatedGraded b) r := by
  apply (associatedGradedAlgEquiv b).injective
  rw [associatedGradedAlgEquiv_symbol, AlgEquiv.commutes]
  change MvPolynomial.homogeneousComponent 0
    (polynomialCoordinates b (algebraMap R U r)) = algebraMap R P r
  rw [
    Algebra.algebraMap_eq_smul_one, map_smul, polynomialCoordinates_one, map_smul]
  simp only [MvPolynomial.homogeneousComponent_zero, MvPolynomial.coeff_one,
    ite_true, MvPolynomial.C_1, Algebra.algebraMap_eq_smul_one]

/-- For an ordered basis b : Basis I R L of an R-Lie algebra over a commutative ring R,
symbol_0(1_U) = 1_AssociatedGraded(b). The unit 1_U belongs to D_0 and is taken modulo the
zero lower stage before insertion into degree zero. -/
theorem symbol_one (b : Module.Basis I R L) :
    symbol b 0 ⟨(1 : U), UniversalEnvelopingAlgebra.one_mem_degreeFiltration R L 0⟩ = 1 := by
  simpa only [map_one] using symbol_algebraMap b (1 : R)

/-- Let b : Basis I R L be an ordered basis of an R-Lie algebra over a commutative ring R, and n ∈
ℕ. Define the degree-n component of AssociatedGraded(b) as the inverse image of the
homogeneous degree-n polynomial submodule under the R-linear map of
associatedGradedAlgEquiv(b). Thus an element lies in this component exactly when its PBW
polynomial coordinate is homogeneous of degree n. -/
def associatedGradedComponent (b : Module.Basis I R L) (n : ℕ) : Submodule R (AssociatedGraded b) :=
  (MvPolynomial.homogeneousSubmodule I R n).comap (associatedGradedAlgEquiv b).toLinearMap

/-- For an ordered basis b : Basis I R L over a commutative ring R and n ∈ ℕ, the component
associatedGradedComponent(b,n) equals the R-linear range of ofGradedLayer(b,n). Equivalently,
the homogeneous degree-n elements in the full PBW coordinate algebra are exactly those
obtained by inserting elements of D_n/D_{<n}. -/
theorem associatedGradedComponent_eq_range (b : Module.Basis I R L) (n : ℕ) :
    associatedGradedComponent b n = LinearMap.range (ofGradedLayer b n) := by
  ext x
  constructor
  · intro hx
    let p : MvPolynomial.homogeneousSubmodule I R n := ⟨associatedGradedAlgEquiv b x, hx⟩
    refine ⟨(completeGradedEquiv b n).symm p, ?_⟩
    apply (associatedGradedAlgEquiv b).injective
    rw [associatedGradedAlgEquiv_ofGradedLayer, LinearEquiv.apply_symm_apply]
  · rintro ⟨y, rfl⟩
    change associatedGradedAlgEquiv b (ofGradedLayer b n y) ∈
      MvPolynomial.homogeneousSubmodule I R n
    rw [associatedGradedAlgEquiv_ofGradedLayer]
    exact (completeGradedEquiv b n y).property

attribute [local instance] MvPolynomial.gradedAlgebra

instance associatedGradedComponent_gradedMonoid (b : Module.Basis I R L) :
    SetLike.GradedMonoid (associatedGradedComponent b) where
  one_mem := by
    change associatedGradedAlgEquiv b 1 ∈ MvPolynomial.homogeneousSubmodule I R 0
    rw [map_one]
    exact SetLike.one_mem_graded (MvPolynomial.homogeneousSubmodule I R)
  mul_mem := by
    intro n m x y hx hy
    change associatedGradedAlgEquiv b (x * y) ∈ MvPolynomial.homogeneousSubmodule I R (n + m)
    rw [map_mul]
    exact SetLike.mul_mem_graded hx hy

/-- Let R be a commutative ring, L an R-Lie algebra, b : Basis I R L with LinearOrder I, and n ∈
ℕ. Restricting the full PBW R-algebra coordinate equivalence gives an R-linear equivalence
between associatedGradedComponent(b,n) and the homogeneous degree-n submodule of MvPolynomial
I R. Its inverse restricts the inverse polynomial equivalence to that homogeneous submodule. -/
def associatedGradedComponentEquiv (b : Module.Basis I R L) (n : ℕ) :
    associatedGradedComponent b n ≃ₗ[R] MvPolynomial.homogeneousSubmodule I R n where
  toFun x := ⟨associatedGradedAlgEquiv b x.val, x.property⟩
  invFun p := ⟨(associatedGradedAlgEquiv b).symm p.val, by
    change associatedGradedAlgEquiv b ((associatedGradedAlgEquiv b).symm p.val) ∈
      MvPolynomial.homogeneousSubmodule I R n
    rw [AlgEquiv.apply_symm_apply]
    exact p.property⟩
  left_inv x := by apply Subtype.ext; exact (associatedGradedAlgEquiv b).symm_apply_apply x.val
  right_inv p := by apply Subtype.ext; exact (associatedGradedAlgEquiv b).apply_symm_apply p.val
  map_add' x y := by apply Subtype.ext; exact map_add (associatedGradedAlgEquiv b) x.val y.val
  map_smul' r x := by apply Subtype.ext; exact map_smul (associatedGradedAlgEquiv b) r x.val

/-- For an ordered basis b : Basis I R L of an R-Lie algebra over a commutative ring R, there is
an R-linear equivalence AssociatedGraded(b) ≃ₗ[R] ⊕_n associatedGradedComponent(b,n). It
decomposes the polynomial coordinate into its homogeneous pieces and then returns each piece
to the corresponding associated graded component. Each element has only finitely many nonzero
components. -/
def associatedGradedDecomposeEquiv (b : Module.Basis I R L) :
    AssociatedGraded b ≃ₗ[R] ⨁ n, associatedGradedComponent b n :=
  (associatedGradedAlgEquiv b).toLinearEquiv.trans
    ((DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule I R)).trans
      (DirectSum.congrLinearEquiv (associatedGradedComponentEquiv b)).symm)

/-- Let b : Basis I R L be an ordered basis over a commutative ring R. The inverse of the
homogeneous decomposition equivalence, as an R-linear map, equals DirectSum.coeLinearMap for
the family associatedGradedComponent(b,n). Hence a finite family of homogeneous components is
reassembled by summing their inclusions into AssociatedGraded(b). -/
theorem associatedGradedDecomposeEquiv_symm_eq_coe (b : Module.Basis I R L) :
    (associatedGradedDecomposeEquiv b).symm.toLinearMap =
      DirectSum.coeLinearMap (associatedGradedComponent b) := by
  apply LinearMap.ext
  intro z
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n x =>
      rw [DirectSum.coeLinearMap_of]
      change (associatedGradedAlgEquiv b).symm
        ((DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule I R)).symm
          (DirectSum.lmap (fun n => (associatedGradedComponentEquiv b n).toLinearMap)
             (DirectSum.lof R ℕ (fun n => associatedGradedComponent b n) n x))) = x.val
      rw [DirectSum.lmap_lof, DirectSum.decomposeLinearEquiv_symm_lof]
      exact (associatedGradedAlgEquiv b).symm_apply_apply x.val
  | add x y hx hy => simp only [map_add, hx, hy]

instance associatedGradedComponentDecomposition (b : Module.Basis I R L) :
    DirectSum.Decomposition (associatedGradedComponent b) :=
  (DirectSum.Decomposition.ofLinearMap (associatedGradedComponent b)
    (associatedGradedDecomposeEquiv b).toLinearMap
    (by
      rw [← associatedGradedDecomposeEquiv_symm_eq_coe]
      apply LinearMap.ext
      intro x
      exact (associatedGradedDecomposeEquiv b).symm_apply_apply x)
    (by
      rw [← associatedGradedDecomposeEquiv_symm_eq_coe]
      apply LinearMap.ext
      intro x
      exact (associatedGradedDecomposeEquiv b).apply_symm_apply x))

/-- Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L with LinearOrder I. The
submodules associatedGradedComponent(b,n) form an ℕ-graded algebra structure on
AssociatedGraded(b). Their products have degree n+m, the unit has degree zero, and the
homogeneous decomposition is a finite-support direct-sum decomposition. -/
instance associatedGradedGradedAlgebra (b : Module.Basis I R L) :
    GradedAlgebra (associatedGradedComponent b) :=
  { (inferInstance : SetLike.GradedMonoid (associatedGradedComponent b)),
    (inferInstance : DirectSum.Decomposition (associatedGradedComponent b)) with }

/-- For an ordered basis b : Basis I R L over a commutative ring R, n ∈ ℕ, and x ∈
AssociatedGraded(b), associatedGradedAlgEquiv(b)(x) belongs to the homogeneous degree-n
polynomial submodule if and only if x belongs to associatedGradedComponent(b,n). This
equivalence identifies the grading on the quotient carrier with polynomial total-degree
grading. -/
theorem associatedGradedAlgEquiv_mem_component_iff (b : Module.Basis I R L) (n : ℕ)
    (x : AssociatedGraded b) :
    associatedGradedAlgEquiv b x ∈ MvPolynomial.homogeneousSubmodule I R n ↔
      x ∈ associatedGradedComponent b n := Iff.rfl

end UniversalEnvelopingAlgebra.PBW
