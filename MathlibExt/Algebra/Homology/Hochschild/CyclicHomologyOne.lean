/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.RingTheory.Kaehler.HochschildPresentation
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.MixedBicomplex
public import MathlibExt.Algebra.Homology.ChainComplex.MixedBicomplex.HomologyOne
public import MathlibExt.Algebra.Homology.Functor
public import MathlibExt.Algebra.Homology.TotalComplexFirstColumn
public import Mathlib.Algebra.Algebra.Tower

/-!
# Degree-one cyclic homology and exact differential forms

Let k be a commutative ring and A a commutative unital k-algebra.
There is a k-linear isomorphism
HC_1(A/k) ≅ Ω_{A/k} / Im_k(d),
where d : A → Ω_{A/k} is the universal k-derivation and the quotient
uses its k-linear image. The comparison sends the cyclic tensor class
[a ⊗ b] to [a db], and its inverse sends [a db] to that tensor class.

In ordered tensor coordinates, the regular Hochschild boundary is
b_2(a ⊗ b ⊗ c) = ab ⊗ c − a ⊗ bc + ca ⊗ b.
The degree-one mixed presentation has first arrow
C_2 ⊕ C_0 → C_1, (x,y) ↦ b_2(x) + B_0(y), and b_1 = 0.
The stored Connes value is B_0(a) = 1 ⊗ a + a ⊗ 1; modulo the
b_2-image it represents da.

The one- and two-factor tensor coordinate isomorphisms hold for any
semimodule over a commutative semiring. For a nonunital associative
k-bilinear ring, the Hochschild complex still maps to the cyclic total
through its first column, naturally after common carrier lifting.
For unital commutative algebras, the degree-one quotient isomorphism
is natural in algebra homomorphisms. Its categorical target is the
whole-module lift ULift.{u} Q_A in ModuleCat at max{u,v}.

References: J.-L. Loday, Cyclic Homology, Proposition 2.1.14 and
Corollary 2.1.10.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace ModuleCat.Algebra.Hochschild

universe u v w

section Coordinates

variable (k : Type u) (A : Type v) [CommSemiring k] [AddCommMonoid A] [Module k A]

/-- Let k be a commutative semiring and A a k-semimodule.
The singleton tensor coordinates give the k-linear equivalence
A ⊗[k] A^{⊗1} ≃ A ⊗[k] A, retaining the first and single
tail factors in order. -/
def chainOneEquiv : A ⊗[k] TensorPower k 1 A ≃ₗ[k] A ⊗[k] A :=
  TensorProduct.congr (LinearEquiv.refl k A)
    (PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : Fin 1 => A) 0)

/-- Let k be a commutative semiring and A a k-semimodule.
For a ∈ A and s : Fin 1 → A, the singleton coordinate
isomorphism sends a ⊗ tprod(s) to a ⊗ s_0. -/
lemma chainOneEquiv_tprod (a : A) (s : Fin 1 → A) :
    chainOneEquiv k A (a ⊗ₜ[k] PiTensorProduct.tprod k s) = a ⊗ₜ[k] s 0 := by
  simp only [chainOneEquiv, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    PiTensorProduct.subsingletonEquiv_apply_tprod]

/-- Let k be a commutative semiring and A a k-semimodule.
The inverse singleton coordinate isomorphism sends a ⊗ b to
a ⊗ tprod(j ↦ b), for the one-entry family on Fin 1. -/
lemma chainOneEquiv_symm_tmul (a b : A) :
    (chainOneEquiv k A).symm (a ⊗ₜ[k] b) =
      a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => b) := by
  apply (chainOneEquiv k A).injective
  rw [LinearEquiv.apply_symm_apply, chainOneEquiv_tprod]

/-- Let k be a commutative semiring and A a k-semimodule.
The ordered degree-two tensor coordinates give a k-linear
equivalence A ⊗[k] A^{⊗2} ≃ A ⊗[k] (A ⊗[k] A). -/
def chainTwoEquiv : A ⊗[k] TensorPower k 2 A ≃ₗ[k] A ⊗[k] (A ⊗[k] A) :=
  TensorProduct.congr (LinearEquiv.refl k A)
    ((TensorPower.consEquiv k A 1).symm.trans (chainOneEquiv k A))

/-- Let k be a commutative semiring and A a k-semimodule.
For a ∈ A and s : Fin 2 → A, the two-tail coordinate
isomorphism sends a ⊗ tprod(s) to a ⊗ (s_0 ⊗ s_1). -/
lemma chainTwoEquiv_tprod (a : A) (s : Fin 2 → A) :
    chainTwoEquiv k A (a ⊗ₜ[k] PiTensorProduct.tprod k s) =
      a ⊗ₜ[k] (s 0 ⊗ₜ[k] s 1) := by
  change (TensorProduct.congr (LinearEquiv.refl k A)
      ((TensorPower.consEquiv k A 1).symm.trans (chainOneEquiv k A)))
        (a ⊗ₜ[k] PiTensorProduct.tprod k s) = _
  rw [TensorProduct.congr_tmul]
  change a ⊗ₜ[k] chainOneEquiv k A
      ((TensorPower.consEquiv k A 1).symm (PiTensorProduct.tprod k s)) = _
  rw [TensorPower.consEquiv_symm_tprod, chainOneEquiv_tprod]
  have hTail : Fin.tail s 0 = s 1 := rfl
  exact congrArg (fun b : A => a ⊗ₜ[k] (s 0 ⊗ₜ[k] b)) hTail

end Coordinates

section OriginalBoundary

variable (k : Type u) (A : Type v) [CommRing k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- Let k be a commutative ring and A a nonunital associative ring
with k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}
and let T be the total of its cyclic b/b′ bicomplex.
In ordered coordinates, the regular Hochschild boundary has value
b_2(a ⊗ b ⊗ c) = ab ⊗ c − a ⊗ bc + ca ⊗ b.
The last multiplication keeps the order ca. -/
lemma regularBoundaryTwo_tprod (a : A) (s : Fin 2 → A) :
    ((NonUnital.bComplex k A).d 2 1).hom (a ⊗ₜ[k] PiTensorProduct.tprod k s) =
      (a * s 0) ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => s 1) -
        a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => s 0 * s 1) +
        (s 1 * a) ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => s 0) := by
  have hFirst : hochschildDropFirst s = (fun _ : Fin 1 => s 1) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have hMiddle : hochschildMulAdjacent (0 : Fin 1) s =
      (fun _ : Fin 1 => s 0 * s 1) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have hLast : hochschildDropLast s = (fun _ : Fin 1 => s 0) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  rw [NonUnital.bComplex_d, Fin.sum_univ_three]
  simp only [ModuleCat.hom_add, ModuleCat.hom_zsmul, LinearMap.add_apply,
    LinearMap.smul_apply, Fin.val_zero, Fin.val_one, pow_zero, pow_one, pow_two,
    neg_mul_neg, one_mul, one_smul, neg_one_smul, ModuleCat.hom_neg, LinearMap.neg_apply]
  have hsign : (-1 : ℤ) ^ (2 : Fin 3).val = 1 := by decide
  erw [hsign, one_smul, ← sub_eq_add_neg]
  change (NonUnital.regularFace k A 1 0).hom (a ⊗ₜ[k] PiTensorProduct.tprod k s) -
      (NonUnital.regularFace k A 1 (0 : Fin 1).castSucc.succ).hom
        (a ⊗ₜ[k] PiTensorProduct.tprod k s) +
      (NonUnital.regularFace k A 1 (Fin.last 2)).hom
        (a ⊗ₜ[k] PiTensorProduct.tprod k s) = _
  rw [NonUnital.regularFace_first_tprod, NonUnital.regularFace_inner_tprod,
    NonUnital.regularFace_last_tprod, hFirst, hMiddle, hLast]
  rfl

/-- Let k be a commutative ring and A a nonunital associative ring
with k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}
and let T be the total of its cyclic b/b′ bicomplex.
If I_n : C_n → T_n is the column-zero coprojection, then
d_T I_{n+1} = I_n b_{n+1}. Thus column zero has the regular
Hochschild differential. -/
lemma regularCyclicColumn_d (n : ℕ) :
    (NonUnital.cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) 0 (n + 1) (n + 1)
        (Nat.zero_add (n + 1)) ≫ (NonUnital.cyclicTotal k A).d (n + 1) n =
      (NonUnital.bComplex k A).d (n + 1) n ≫
        (NonUnital.cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) 0 n n
          (Nat.zero_add n) := by
  let R := NonUnital.cyclicBicomplex k A
  have hNative := HomologicalComplex₂.ιTotal_firstColumn_d R n
  have hColumn : (R.X 0).d (n + 1) n = (NonUnital.bComplex k A).d (n + 1) n :=
    (NonUnital.cyclicBicomplex_vertical k A 0 n).trans
      (if_pos (show Even (0 : ℕ) from ⟨0, rfl⟩))
  exact hNative.trans (congrArg (fun d => d ≫
    R.ιTotal (ComplexShape.down ℕ) 0 n n (Nat.zero_add n)) hColumn)

/-- Let k be a commutative ring and A a nonunital associative ring
with k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}
and let T be the total of its cyclic b/b′ bicomplex.
The column-zero coprojections I_n define a chain map
I : C_*(A) → T_*(A) from the regular Hochschild complex to
the cyclic total. -/
def regularCyclicChainMap : NonUnital.bComplex k A ⟶ NonUnital.cyclicTotal k A :=
  eqToHom (NonUnital.cyclicColumn_even k A 0 (show Even (0 : ℕ) from ⟨0, rfl⟩)).symm ≫
    HomologicalComplex₂.firstColumnTotalInclusion (NonUnital.cyclicBicomplex k A)

/-- Let k be a commutative ring and A a nonunital associative ring
with k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}
and let T be the total of its cyclic b/b′ bicomplex.
The degree-n component of I : C_*(A) → T_*(A) is precisely
the coprojection of column zero and row n into total degree n. -/
lemma regularCyclicChainMap_f (n : ℕ) :
    (regularCyclicChainMap k A).f n =
      (NonUnital.cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) 0 n n
        (Nat.zero_add n) := by
  change (eqToHom (NonUnital.cyclicColumn_even k A 0
      (show Even (0 : ℕ) from ⟨0, rfl⟩)).symm).f n ≫
        (HomologicalComplex₂.firstColumnTotalInclusion (NonUnital.cyclicBicomplex k A)).f n = _
  rw [HomologicalComplex.eqToHom_f,
    HomologicalComplex₂.firstColumnTotalInclusion_f]
  change (𝟙 ((NonUnital.bComplex k A).X n)) ≫
    (NonUnital.cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) 0 n n (Nat.zero_add n) = _
  exact Category.id_comp _

/-- Let k be a commutative ring and A a nonunital associative ring
with k-bilinear multiplication. Put C_n = A ⊗[k] A^{⊗n}
and let T be the total of its cyclic b/b′ bicomplex.
Under the identification of cyclic column zero with C_*(A),
the chain map I is the total-complex inclusion of that first column. -/
lemma regularCyclicChainMap_eq_firstColumn :
    regularCyclicChainMap k A =
      eqToHom (NonUnital.cyclicColumn_even k A 0
        (show Even (0 : ℕ) from ⟨0, rfl⟩)).symm ≫
          HomologicalComplex₂.firstColumnTotalInclusion (NonUnital.cyclicBicomplex k A) := rfl

/-- Let k : Type u be a commutative ring and A : Type v a nonunital
associative ring with k-bilinear multiplication. For any additional
lift height ℓ, applying ULift to the Hochschild terms and cyclic
bicomplex gives a first-column chain inclusion
U^ℓ C_*(A) → Tot(U^ℓ K(A)) in carrier universe max{u,v,ℓ}. -/
def regularCyclicChainMapLift.{xCL, uCL, vCL} (k : Type uCL) [CommRing k] (A : Type vCL) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] :
    ((ModuleCat.uliftFunctor.{xCL, max uCL vCL} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (NonUnital.bComplex k A) ⟶
        (HomologicalComplex₂.total ((((ModuleCat.uliftFunctor.{xCL, max uCL vCL} k).mapHomologicalComplex
          (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (NonUnital.cyclicBicomplex k A)) (ComplexShape.down ℕ)) :=
  ((ModuleCat.uliftFunctor.{xCL, max uCL vCL} k).mapHomologicalComplex
    (ComplexShape.down ℕ)).map (regularCyclicChainMap k A) ≫
      (NonUnital.cyclicTotalLiftIso.{xCL} k A).hom

/-- Let k : Type u be commutative and A : Type v a nonunital
associative k-bilinear ring. At any lift height ℓ, the degree-n
component of the lifted Hochschild-to-cyclic chain map is the
column-zero, row-n coprojection into Tot(U^ℓ K(A)). -/
lemma regularCyclicChainMapLift_f.{xCF, uCF, vCF}
    (k : Type uCF) [CommRing k] (A : Type vCF) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (regularCyclicChainMapLift.{xCF} k A).f n =
      (HomologicalComplex₂.ιTotal ((((ModuleCat.uliftFunctor.{xCF, max uCF vCF} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (NonUnital.cyclicBicomplex k A)) (ComplexShape.down ℕ) 0 n n
            (Nat.zero_add n)) := by
  change (ModuleCat.uliftFunctor.{xCF, max uCF vCF} k).map ((regularCyclicChainMap k A).f n) ≫
    (NonUnital.cyclicTotalLiftIso.{xCF} k A).hom.f n = _
  rw [regularCyclicChainMap_f]
  exact NonUnital.map_cyclicInclusion_lift k A 0 n n (Nat.zero_add n)

section FirstColumnMaps

variable {k A} {B : Type w} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Let k be commutative and A,B nonunital associative rings with
k-bilinear multiplication, in independent universes v,w. A
multiplicative k-linear map f : A → B gives a map K(f) between
their cyclic bicomplexes in common height max{u,v,w}.
The lifted first-column inclusions satisfy
Tot(K(f)) I_A = I_B K(f)_0,
where A is lifted by w and B by v. -/
lemma regularCyclicChainMapLift_naturality (f : A →ₙₐ[k] B) :
    regularCyclicChainMapLift.{w} k A ≫
        HomologicalComplex₂.total.map (NonUnital.cyclicBicomplexMap f)
          (ComplexShape.down ℕ) =
      (NonUnital.cyclicBicomplexMap f).f 0 ≫ regularCyclicChainMapLift.{v} k B := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let PA : HomologicalComplex₂ (ModuleCat.{max u v w} k)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    ((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (NonUnital.cyclicBicomplex k A)
  let PB : HomologicalComplex₂ (ModuleCat.{max u v w} k)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    ((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (NonUnital.cyclicBicomplex k B)
  let φ : PA ⟶ PB := NonUnital.cyclicBicomplexMap f
  let c := HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)
  have hA : regularCyclicChainMapLift.{w} k A =
      HomologicalComplex₂.firstColumnTotalInclusion PA := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [regularCyclicChainMapLift_f, HomologicalComplex₂.firstColumnTotalInclusion_f]
  have hB : regularCyclicChainMapLift.{v} k B =
      HomologicalComplex₂.firstColumnTotalInclusion PB := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [regularCyclicChainMapLift_f, HomologicalComplex₂.firstColumnTotalInclusion_f]
  change regularCyclicChainMapLift.{w} k A ≫ c = φ.f 0 ≫ regularCyclicChainMapLift.{v} k B
  have hLeft : regularCyclicChainMapLift.{w} k A ≫ c =
      HomologicalComplex₂.firstColumnTotalInclusion PA ≫ c :=
    congrArg (fun j : PA.X 0 ⟶ PA.total (ComplexShape.down ℕ) => j ≫ c) hA
  have hNative : HomologicalComplex₂.firstColumnTotalInclusion PA ≫ c =
      φ.f 0 ≫ HomologicalComplex₂.firstColumnTotalInclusion PB :=
    HomologicalComplex₂.firstColumnTotalInclusion_naturality φ
  have hRight : φ.f 0 ≫ HomologicalComplex₂.firstColumnTotalInclusion PB =
      φ.f 0 ≫ regularCyclicChainMapLift.{v} k B :=
    congrArg (fun j : PB.X 0 ⟶ PB.total (ComplexShape.down ℕ) => φ.f 0 ≫ j) hB.symm
  exact hLeft.trans (hNative.trans hRight)

end FirstColumnMaps

end OriginalBoundary

section Commutative

variable (k : Type u) (A : Type v) [CommRing k] [CommRing A] [Algebra k A]

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
The regular Hochschild boundary b_1 : C_1 → C_0 is zero,
since b_1(a ⊗ b) = ab − ba and A is commutative. -/
lemma regularBoundaryOne_eq_zero : (NonUnital.bComplex k A).d 1 0 = 0 := by
  apply ModuleCat.hom_ext
  apply tensorPower_ext
  intro a s
  rw [NonUnital.bComplex_d, Fin.sum_univ_two]
  simp only [ModuleCat.hom_add, ModuleCat.hom_zsmul, LinearMap.add_apply,
    LinearMap.smul_apply, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_one_smul]
  change (NonUnital.regularFace k A 0 0).hom (a ⊗ₜ[k] PiTensorProduct.tprod k s) -
      (NonUnital.regularFace k A 0 (Fin.last 1)).hom
        (a ⊗ₜ[k] PiTensorProduct.tprod k s) = 0
  rw [NonUnital.regularFace_first_tprod, NonUnital.regularFace_last_tprod]
  have h : hochschildDropFirst s = hochschildDropLast s := by
    funext i
    exact Fin.elim0 i
  rw [h, mul_comm a (s 0)]
  have hLast : s (Fin.last 0) = s 0 := rfl
  erw [hLast, sub_self]

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
The coordinate maps κ_1 : C_1 ≃ A ⊗[k] A and
κ_2 : C_2 ≃ A ⊗[k] (A ⊗[k] A) satisfy
κ_1 b_2 = b_2^Ω κ_2, where
b_2^Ω(a ⊗ (b ⊗ c)) = ab ⊗ c − a ⊗ bc + ca ⊗ b
is the Kähler presentation relation. -/
lemma regularBoundaryTwo_eq :
    (chainOneEquiv k A).toLinearMap.comp ((NonUnital.bComplex k A).d 2 1).hom =
      ((KaehlerDifferential.Hochschild.boundaryTwo k A).restrictScalars k).comp
        (chainTwoEquiv k A).toLinearMap := by
  apply tensorPower_ext
  intro a s
  change chainOneEquiv k A
      (((NonUnital.bComplex k A).d 2 1).hom (a ⊗ₜ[k] PiTensorProduct.tprod k s)) =
    KaehlerDifferential.Hochschild.boundaryTwo k A
      (chainTwoEquiv k A (a ⊗ₜ[k] PiTensorProduct.tprod k s))
  rw [regularBoundaryTwo_tprod, map_add, map_sub, chainOneEquiv_tprod,
    chainOneEquiv_tprod, chainOneEquiv_tprod, chainTwoEquiv_tprod,
    KaehlerDifferential.Hochschild.boundaryTwo_tmul]

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
In degree-one tensor coordinates, the Connes boundary on a ∈ A
has the two positive endpoint terms
B_0(a) = 1 ⊗ a + a ⊗ 1. -/
lemma chainOneEquiv_connesBoundary_zero (a : A) :
    chainOneEquiv k A ((NonUnital.connesBoundary k A 0).hom
      (a ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 0 => Fin.elim0 i))) =
        1 ⊗ₜ[k] a + a ⊗ₜ[k] 1 := by
  rw [NonUnital.connesBoundary, NonUnital.connesBoundaryWith_zero_tprod,
    map_add, chainOneEquiv_tprod, chainOneEquiv_tprod]

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
After quotienting C_1 by the b_2-image and identifying the quotient
with Ω_A by a ⊗ b ↦ a db, the Connes class B_0(a) maps
to d_A a. The term a d_A(1) is zero. -/
lemma toKaehler_connesBoundary_zero (a : A) :
    KaehlerDifferential.Hochschild.toKaehler k A
      (KaehlerDifferential.Hochschild.quotientMap k A
        (chainOneEquiv k A ((NonUnital.connesBoundary k A 0).hom
          (a ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 0 => Fin.elim0 i))))) =
      KaehlerDifferential.D k A a := by
  rw [chainOneEquiv_connesBoundary_zero, map_add, map_add,
    KaehlerDifferential.Hochschild.toKaehler_tmul,
    KaehlerDifferential.Hochschild.toKaehler_tmul,
    Derivation.map_one_eq_zero, smul_zero, one_smul, add_zero]

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
The exact-differential quotient is Q_A = Ω_A / Im_k(d_A).
The range is taken for the k-linear derivation, so this construction
is a quotient k-module. -/
abbrev KaehlerExactQuotient : Type v :=
  KaehlerDifferential k A ⧸ LinearMap.range (KaehlerDifferential.D k A).toLinearMap

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
The k-linear quotient map Ω_A → Q_A sends a differential form
ω to its class [ω] modulo the exact differentials. -/
def kaehlerClass : KaehlerDifferential k A →ₗ[k] KaehlerExactQuotient k A :=
  (LinearMap.range (KaehlerDifferential.D k A).toLinearMap).mkQ

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
The k-linear tensor representative τ_A : C_1 → Q_A is
τ_A(a ⊗ b) = [a d_A b], under singleton tensor coordinates. -/
def cyclicOneRepresentative : A ⊗[k] TensorPower k 1 A →ₗ[k] KaehlerExactQuotient k A :=
  (kaehlerClass k A).comp
    (((KaehlerDifferential.D k A).tensorProductTo.restrictScalars k).comp
      (chainOneEquiv k A).toLinearMap)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
For a ∈ A and s : Fin 1 → A, the tensor representative
satisfies τ_A(a ⊗ tprod(s)) = [a d_A(s_0)]. -/
lemma cyclicOneRepresentative_tprod (a : A) (s : Fin 1 → A) :
    cyclicOneRepresentative k A (a ⊗ₜ[k] PiTensorProduct.tprod k s) =
      kaehlerClass k A (a • KaehlerDifferential.D k A (s 0)) := by
  change kaehlerClass k A ((KaehlerDifferential.D k A).tensorProductTo
    (chainOneEquiv k A (a ⊗ₜ[k] PiTensorProduct.tprod k s))) = _
  rw [chainOneEquiv_tprod, Derivation.tensorProductTo_tmul]

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
The tensor representative annihilates the degree-two Hochschild
boundary: τ_A b_2 = 0. The relation is
[ab dc − a d(bc) + ca db] = 0. -/
lemma cyclicOneRepresentative_comp_boundaryTwo :
    (cyclicOneRepresentative k A).comp ((NonUnital.bComplex k A).d 2 1).hom = 0 := by
  apply LinearMap.ext
  intro x
  have hb : chainOneEquiv k A (((NonUnital.bComplex k A).d 2 1).hom x) =
      KaehlerDifferential.Hochschild.boundaryTwo k A (chainTwoEquiv k A x) :=
    LinearMap.congr_fun (regularBoundaryTwo_eq k A) x
  have hD : (KaehlerDifferential.D k A).tensorProductTo
      (KaehlerDifferential.Hochschild.boundaryTwo k A (chainTwoEquiv k A x)) = 0 :=
    LinearMap.congr_fun
      (KaehlerDifferential.Hochschild.boundaryTwo_comp_tensorProductTo k A)
      (chainTwoEquiv k A x)
  change kaehlerClass k A ((KaehlerDifferential.D k A).tensorProductTo
    (chainOneEquiv k A (((NonUnital.bComplex k A).d 2 1).hom x))) = 0
  rw [hb, hD, map_zero]

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
The tensor representative annihilates the Connes zero boundary:
τ_A B_0 = 0. Its value on B_0(a) is [d_A a], which vanishes
in the k-linear exact-differential quotient. -/
lemma cyclicOneRepresentative_comp_connesBoundary :
    (cyclicOneRepresentative k A).comp (NonUnital.connesBoundary k A 0).hom = 0 := by
  apply tensorPower_ext
  intro a s
  have hs : s = (fun i : Fin 0 => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  subst s
  have hD : (KaehlerDifferential.D k A).tensorProductTo
      (chainOneEquiv k A ((NonUnital.connesBoundary k A 0).hom
        (a ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 0 => Fin.elim0 i)))) =
      KaehlerDifferential.D k A a :=
    (KaehlerDifferential.Hochschild.toKaehler_quotientMap k A _).symm.trans
      (toKaehler_connesBoundary_zero k A a)
  change kaehlerClass k A ((KaehlerDifferential.D k A).tensorProductTo
    (chainOneEquiv k A ((NonUnital.connesBoundary k A 0).hom
      (a ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 0 => Fin.elim0 i))))) = 0
  rw [hD, kaehlerClass, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨a, rfl⟩

local notation "S" => ChainComplex.mixedHomologyOneShortComplex
  (NonUnital.bComplex k A) (NonUnital.connesBoundaryHomotopy k A)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
Lifting the tensor representative gives the k-linear map
C_1 → ULift.{u} Q_A, z ↦ ULift(τ_A(z)), with target in
the common module universe max{u,v}. -/
def cyclicOneRepresentativeLift : A ⊗[k] TensorPower k 1 A →ₗ[k]
    ULift.{u} (KaehlerExactQuotient k A) :=
  (ULift.moduleEquiv (R := k) (M := KaehlerExactQuotient k A)).symm.toLinearMap.comp
    (cyclicOneRepresentative k A)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
Let S be the short complex C_2 ⊕ C_0 → C_1 → C_0,
whose first map is (b_2,B_0) and whose second map b_1 is zero.
The lifted representative τ_A^↑ : C_1 → ULift.{u} Q_A
annihilates the first arrow: τ_A^↑ (b_2,B_0) = 0. -/
lemma cyclicOneRepresentative_comp_f : (S).f ≫ ModuleCat.ofHom (cyclicOneRepresentativeLift k A) =
    0 := by
  change biprod.desc ((NonUnital.bComplex k A).d 2 1)
      ((NonUnital.connesBoundaryHomotopy k A).hom 0 1) ≫
        ModuleCat.ofHom (cyclicOneRepresentativeLift k A) = 0
  apply biprod.hom_ext'
  · rw [← Category.assoc, biprod.inl_desc, Limits.comp_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun y : KaehlerExactQuotient k A =>
      (ULift.up y : ULift.{u} (KaehlerExactQuotient k A)))
      (LinearMap.congr_fun (cyclicOneRepresentative_comp_boundaryTwo k A) x)
  · rw [← Category.assoc, biprod.inr_desc, Limits.comp_zero,
      NonUnital.connesBoundaryHomotopy_hom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun y : KaehlerExactQuotient k A =>
      (ULift.up y : ULift.{u} (KaehlerExactQuotient k A)))
      (LinearMap.congr_fun (cyclicOneRepresentative_comp_connesBoundary k A) x)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
The tensor representative τ_A : C_1 → Q_A is surjective.
Every class of a differential form has a degree-one tensor
representative, extended linearly from a ⊗ b ↦ [a db]. -/
lemma cyclicOneRepresentative_surjective : Function.Surjective (cyclicOneRepresentative k A) := by
  intro z
  obtain ⟨ω, hω⟩ :=
    Submodule.mkQ_surjective (LinearMap.range (KaehlerDifferential.D k A).toLinearMap) z
  obtain ⟨t, ht⟩ := KaehlerDifferential.tensorProductTo_surjective k A ω
  refine ⟨(chainOneEquiv k A).symm t, ?_⟩
  change kaehlerClass k A ((KaehlerDifferential.D k A).tensorProductTo
    (chainOneEquiv k A ((chainOneEquiv k A).symm t))) = z
  rw [LinearEquiv.apply_symm_apply, ht]
  change (LinearMap.range (KaehlerDifferential.D k A).toLinearMap).mkQ ω = z
  exact hω

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
Let S be the short complex C_2 ⊕ C_0 → C_1 → C_0,
whose first map is (b_2,B_0) and whose second map b_1 is zero.
The sequence C_2 ⊕ C_0 → C_1 → Q_A is exact at C_1:
ker(τ_A) = im(b_2,B_0). Thus the kernel is the sum of the
Hochschild and Connes boundary images. -/
lemma cyclicOneRepresentative_exact : Function.Exact (S).f.hom (cyclicOneRepresentative k A) := by
  intro x
  constructor
  · intro hx
    have hm : (KaehlerDifferential.D k A).tensorProductTo (chainOneEquiv k A x) ∈
        LinearMap.range (KaehlerDifferential.D k A).toLinearMap := by
      change (LinearMap.range (KaehlerDifferential.D k A).toLinearMap).mkQ
        ((KaehlerDifferential.D k A).tensorProductTo (chainOneEquiv k A x)) = 0 at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      exact hx
    obtain ⟨a, ha⟩ := hm
    let z : (NonUnital.bComplex k A).X 0 :=
      a ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 0 => Fin.elim0 i)
    let β : (S).X₂ := (NonUnital.connesBoundary k A 0).hom z
    have hβ : (KaehlerDifferential.D k A).tensorProductTo (chainOneEquiv k A β) =
        KaehlerDifferential.D k A a :=
      (KaehlerDifferential.Hochschild.toKaehler_quotientMap k A _).symm.trans
        (toKaehler_connesBoundary_zero k A a)
    have hZero : (KaehlerDifferential.D k A).tensorProductTo
        (chainOneEquiv k A (x - β)) = 0 := by
      let F : (S).X₂ →ₗ[k] KaehlerDifferential k A :=
        ((KaehlerDifferential.D k A).tensorProductTo.restrictScalars k).comp
          (chainOneEquiv k A).toLinearMap
      have hxF : F x = KaehlerDifferential.D k A a := ha.symm
      have hβF : F β = KaehlerDifferential.D k A a := hβ
      change F (x - β) = 0
      exact (F.map_sub x β).trans
        ((congrArg₂ (fun x y : KaehlerDifferential k A => x - y) hxF hβF).trans
          (sub_self (KaehlerDifferential.D k A a)))
    obtain ⟨y, hy⟩ :=
      (KaehlerDifferential.Hochschild.boundaryTwo_exact k A _).mp hZero
    let y' : (NonUnital.bComplex k A).X 2 := (chainTwoEquiv k A).symm y
    have hBoundary : ((NonUnital.bComplex k A).d 2 1).hom y' = x - β := by
      apply (chainOneEquiv k A).injective
      have hb : chainOneEquiv k A (((NonUnital.bComplex k A).d 2 1).hom y') =
          KaehlerDifferential.Hochschild.boundaryTwo k A (chainTwoEquiv k A y') :=
        LinearMap.congr_fun (regularBoundaryTwo_eq k A) y'
      exact hb.trans
        ((congrArg (KaehlerDifferential.Hochschild.boundaryTwo k A)
          ((chainTwoEquiv k A).apply_symm_apply y)).trans hy)
    let l : (NonUnital.bComplex k A).X 2 ⟶ (S).X₁ := biprod.inl
    let r : (NonUnital.bComplex k A).X 0 ⟶ (S).X₁ := biprod.inr
    have hLeftMap : l ≫ (S).f = (NonUnital.bComplex k A).d 2 1 :=
      biprod.inl_desc _ _
    have hRightMap : r ≫ (S).f = NonUnital.connesBoundary k A 0 := by
      change biprod.inr ≫ biprod.desc ((NonUnital.bComplex k A).d 2 1)
        ((NonUnital.connesBoundaryHomotopy k A).hom 0 1) = _
      rw [biprod.inr_desc, NonUnital.connesBoundaryHomotopy_hom]
    have hLeft : (S).f.hom (l.hom y') = ((NonUnital.bComplex k A).d 2 1).hom y' :=
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hLeftMap) y'
    have hRight : (S).f.hom (r.hom z) = β :=
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hRightMap) z
    refine ⟨l.hom y' + r.hom z, ?_⟩
    rw [map_add, hLeft, hRight, hBoundary, sub_add_cancel]
  · rintro ⟨y, rfl⟩
    have h := LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (cyclicOneRepresentative_comp_f k A)) y
    exact congrArg ULift.down h

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
Let S be the short complex C_2 ⊕ C_0 → C_1 → C_0,
whose first map is (b_2,B_0) and whose second map b_1 is zero.
The lifted representative τ_A^↑ : C_1 → ULift.{u} Q_A is
a categorical cokernel of (b_2,B_0) in ModuleCat over k at
max{u,v}. -/
def cyclicOneIsCokernel :
    IsColimit (CokernelCofork.ofπ (ModuleCat.ofHom (cyclicOneRepresentativeLift k A))
      (cyclicOneRepresentative_comp_f k A)) := by
  let e : KaehlerExactQuotient k A ≃ₗ[k] ULift.{u} (KaehlerExactQuotient k A) :=
    (ULift.moduleEquiv (R := k) (M := KaehlerExactQuotient k A)).symm
  have hExact : Function.Exact (S).f.hom (cyclicOneRepresentativeLift k A) := by
    intro x
    constructor
    · intro hx
      have hx' : cyclicOneRepresentative k A x = 0 :=
        e.injective (hx.trans (map_zero e).symm)
      exact (cyclicOneRepresentative_exact k A x).mp hx'
    · intro hx
      have hx' : cyclicOneRepresentative k A x = 0 :=
        (cyclicOneRepresentative_exact k A x).mpr hx
      exact (congrArg e hx').trans (map_zero e)
  have hSurjective : Function.Surjective (cyclicOneRepresentativeLift k A) :=
    e.surjective.comp (cyclicOneRepresentative_surjective k A)
  exact ModuleCat.isColimitCokernelCofork (S).f
    (ModuleCat.ofHom (cyclicOneRepresentativeLift k A)) hExact hSurjective

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
Let S be the short complex C_2 ⊕ C_0 → C_1 → C_0,
whose first map is (b_2,B_0) and whose second map b_1 is zero.
The homology of S is k-linearly isomorphic to ULift.{u} Q_A.
It identifies C_1 / (im b_2 + im B_0) with the quotient of
universal differentials by their k-linear exact range. -/
def mixedOneKaehlerIso : (S).homology ≅ ModuleCat.of k (ULift.{u} (KaehlerExactQuotient k A)) :=
  (S).asIsoHomologyι (regularBoundaryOne_eq_zero k A) ≪≫
    ((S).isoOpcyclesOfIsColimit (cyclicOneIsCokernel k A)).symm

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
Let S be the short complex C_2 ⊕ C_0 → C_1 → C_0,
whose first map is (b_2,B_0) and whose second map b_1 is zero.
The canonical quotient from C_1 to H(S), followed by
H(S) ≅ ULift.{u} Q_A, equals the lifted tensor representative
τ_A^↑. -/
@[reassoc]
lemma pOpcycles_mixedOneKaehlerIso :
    (S).pOpcycles ≫ ((S).asIsoHomologyι (regularBoundaryOne_eq_zero k A)).inv ≫
      (mixedOneKaehlerIso k A).hom = ModuleCat.ofHom (cyclicOneRepresentativeLift k A) := by
  change (S).pOpcycles ≫
    ((S).asIsoHomologyι (regularBoundaryOne_eq_zero k A)).inv ≫
      (((S).asIsoHomologyι (regularBoundaryOne_eq_zero k A)).hom ≫
        ((S).isoOpcyclesOfIsColimit (cyclicOneIsCokernel k A)).inv) = _
  rw [Iso.inv_hom_id_assoc]
  exact (S).pOpcycles_π_isoOpcyclesOfIsColimit_inv (cyclicOneIsCokernel k A)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
Let S be the short complex C_2 ⊕ C_0 → C_1 → C_0,
whose first map is (b_2,B_0) and whose second map b_1 is zero.
The homology in degree one of the Connes mixed total is
isomorphic to H(S). Its degree-two boundary is the pair
(b_2,B_0) and its degree-one boundary is b_1 = 0. -/
def connesMixedOnePresentationIso : (NonUnital.connesMixedTotal k A).homology 1 ≅
    (S).homology := by
  let hSquare : ∀ n,
      (NonUnital.connesBoundaryHomotopy k A).hom n (n + 1) ≫
        (NonUnital.connesBoundaryHomotopy k A).hom (n + 1) (n + 2) = 0 := fun n => by
    simpa only [NonUnital.connesBoundaryHomotopy_hom] using
      NonUnital.connesBoundary_square k A n
  change ((ChainComplex.mixedBicomplex (NonUnital.bComplex k A)
      (NonUnital.connesBoundaryHomotopy k A) hSquare).total
        (ComplexShape.down ℕ)).homology 1 ≅ _
  exact ChainComplex.mixedHomologyOneIso (NonUnital.bComplex k A)
    (NonUnital.connesBoundaryHomotopy k A) hSquare

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
The degree-one homology of the Connes mixed total is isomorphic,
as a k-module, to ULift.{u} Q_A through its (b_2,B_0)
presentation. -/
def connesMixedHomologyOneIso : (NonUnital.connesMixedTotal k A).homology 1 ≅
    ModuleCat.of k (ULift.{u} (KaehlerExactQuotient k A)) :=
  connesMixedOnePresentationIso k A ≪≫ mixedOneKaehlerIso k A

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
The first cyclic homology is k-linearly isomorphic to
ULift.{u} Q_A. The isomorphism identifies cyclic degree-one
tensor classes with the classes of a db modulo Im_k(d_A). -/
def cyclicHomologyOneIso : NonUnital.cyclicHomology k A 1 ≅
    ModuleCat.of k (ULift.{u} (KaehlerExactQuotient k A)) :=
  (NonUnital.mixedCyclicHomologyIso k A 1).symm ≪≫ connesMixedHomologyOneIso k A

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
Removing the target whole-module lift gives the k-linear equivalence
HC_1(A/k) ≃ Q_A, with independent ground and algebra universes. -/
def cyclicHomologyOneLinearEquiv :
    NonUnital.cyclicHomology k A 1 ≃ₗ[k] KaehlerExactQuotient k A :=
  (cyclicHomologyOneIso k A).toLinearEquiv.trans
    (ULift.moduleEquiv (R := k) (M := KaehlerExactQuotient k A))

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
The degree-one tensor-class map q_A : C_1 → HC_1(A/k)
sends a Hochschild tensor to its cyclic homology class through
the first cyclic column. -/
def cyclicOneClass : (NonUnital.bComplex k A).X 1 ⟶ NonUnital.cyclicHomology k A 1 :=
  (S).pOpcycles ≫ ((S).asIsoHomologyι (regularBoundaryOne_eq_zero k A)).inv ≫
    (connesMixedOnePresentationIso k A).inv ≫ (NonUnital.mixedCyclicHomologyIso k A 1).hom

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
The tensor-class map q_A : C_1 → HC_1(A/k) is an epimorphism
of k-modules. Every cyclic class has a representative in the full
degree-one tensor module. -/
instance cyclicOneClassEpi : Epi (cyclicOneClass k A) := by
  change Epi ((S).pOpcycles ≫ ((S).asIsoHomologyι (regularBoundaryOne_eq_zero k A)).inv ≫
    (connesMixedOnePresentationIso k A).inv ≫ (NonUnital.mixedCyclicHomologyIso k A 1).hom)
  infer_instance

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
The tensor-class map q_A followed by the isomorphism
E_A : HC_1(A/k) ≅ ULift.{u} Q_A is exactly τ_A^↑. -/
@[reassoc]
lemma cyclicOneClass_comp_cyclicHomologyOneIso :
    cyclicOneClass k A ≫ (cyclicHomologyOneIso k A).hom =
      ModuleCat.ofHom (cyclicOneRepresentativeLift k A) := by
  let e₀ : (S).homology ≅ (S).opcycles := (S).asIsoHomologyι (regularBoundaryOne_eq_zero k A)
  let e₁ : (NonUnital.connesMixedTotal k A).homology 1 ≅ (S).homology :=
    connesMixedOnePresentationIso k A
  let e₂ : (NonUnital.connesMixedTotal k A).homology 1 ≅
      NonUnital.cyclicHomology k A 1 := NonUnital.mixedCyclicHomologyIso k A 1
  let e₃ : (S).homology ≅ ModuleCat.of k (ULift.{u} (KaehlerExactQuotient k A)) := mixedOneKaehlerIso k A
  change ((S).pOpcycles ≫ e₀.inv ≫ e₁.inv ≫ e₂.hom) ≫
    (e₂.inv ≫ e₁.hom ≫ e₃.hom) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  exact pOpcycles_mixedOneKaehlerIso k A

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
On a ∈ A and s : Fin 1 → A, the isomorphism to the lifted
quotient has value E_A(q_A(a ⊗ tprod(s))) = ULift([a d_A(s_0)]). -/
lemma cyclicHomologyOneIso_class_tprod (a : A) (s : Fin 1 → A) :
    (cyclicHomologyOneIso k A).hom.hom
      ((cyclicOneClass k A).hom (a ⊗ₜ[k] PiTensorProduct.tprod k s)) =
        ULift.up (kaehlerClass k A (a • KaehlerDifferential.D k A (s 0))) :=
  (LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (cyclicOneClass_comp_cyclicHomologyOneIso k A))
      (a ⊗ₜ[k] PiTensorProduct.tprod k s)).trans
        (congrArg (fun y : KaehlerExactQuotient k A =>
          (ULift.up y : ULift.{u} (KaehlerExactQuotient k A)))
          (cyclicOneRepresentative_tprod k A a s))

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
The inverse of E_A : HC_1(A/k) ≅ ULift.{u} Q_A sends
ULift([a db]) to q_A(a ⊗ tprod(j ↦ b)), for a,b ∈ A. -/
lemma cyclicHomologyOneIso_inv_class (a b : A) :
    (cyclicHomologyOneIso k A).inv.hom
      (ULift.up (kaehlerClass k A (a • KaehlerDifferential.D k A b))) =
        (cyclicOneClass k A).hom
          (a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => b)) := by
  have h := cyclicHomologyOneIso_class_tprod k A a (fun _ : Fin 1 => b)
  exact (congrArg (cyclicHomologyOneIso k A).inv.hom h).symm.trans
    (ModuleCat.inv_hom_apply (cyclicHomologyOneIso k A)
      ((cyclicOneClass k A).hom
        (a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => b))))

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
The equivalence E_A : HC_1(A/k) ≃ Q_A
satisfies E_A(q_A(z)) = τ_A(z) for every z ∈ C_1. -/
lemma cyclicOneClass_linearEquiv (x : (NonUnital.bComplex k A).X 1) :
    cyclicHomologyOneLinearEquiv k A ((cyclicOneClass k A).hom x) =
      cyclicOneRepresentative k A x := by
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (cyclicOneClass_comp_cyclicHomologyOneIso k A)) x
  exact congrArg ULift.down h

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
The equivalence sends the cyclic tensor class
q_A(a ⊗ tprod(s)) to [a d_A(s_0)], for a ∈ A and s : Fin 1 → A. -/
lemma cyclicHomologyOneLinearEquiv_class_tprod (a : A) (s : Fin 1 → A) :
    cyclicHomologyOneLinearEquiv k A
      ((cyclicOneClass k A).hom (a ⊗ₜ[k] PiTensorProduct.tprod k s)) =
      kaehlerClass k A (a • KaehlerDifferential.D k A (s 0)) :=
  (cyclicOneClass_linearEquiv k A _).trans (cyclicOneRepresentative_tprod k A a s)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Write Q_A = Ω_A / Im_k(d_A), the quotient as a k-module.
The inverse equivalence Q_A ≃ HC_1(A/k)
sends [a db] to q_A(a ⊗ tprod(j ↦ b)). -/
lemma cyclicHomologyOneLinearEquiv_inv_class (a b : A) :
    (cyclicHomologyOneLinearEquiv k A).symm
      (kaehlerClass k A (a • KaehlerDifferential.D k A b)) =
      (cyclicOneClass k A).hom (a ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => b)) := by
  have h := cyclicHomologyOneLinearEquiv_class_tprod k A a (fun _ : Fin 1 => b)
  exact (congrArg (cyclicHomologyOneLinearEquiv k A).symm h).symm.trans
    ((cyclicHomologyOneLinearEquiv k A).symm_apply_apply _)

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Since b_1 = 0, every element of C_1 is a cycle. The map
q_H : C_1 → HH_1(A/k) is its homology-class map, quotienting
by the image of b_2. -/
def regularHomologyOneClass : (NonUnital.bComplex k A).X 1 ⟶
    (NonUnital.bComplex k A).homology 1 :=
  ((NonUnital.bComplex k A).sc' 2 1 0).pOpcycles ≫
    (((NonUnital.bComplex k A).sc' 2 1 0).asIsoHomologyι
      (regularBoundaryOne_eq_zero k A)).inv ≫
        ((NonUnital.bComplex k A).homologyIsoSc' 2 1 0
          ((ComplexShape.down ℕ).prev_eq' (by show (ComplexShape.down ℕ).Rel 2 1; rfl))
          ((ComplexShape.down ℕ).next_eq' (by show (ComplexShape.down ℕ).Rel 1 0; rfl))).inv

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
The first cyclic-column inclusion induces the k-module map
I_* : HH_1(A/k) → HC_1(A/k). -/
def regularCyclicOneMap : (NonUnital.bComplex k A).homology 1 ⟶
    NonUnital.cyclicHomology k A 1 :=
  HomologicalComplex.homologyMap
    (ChainComplex.mixedColumnZeroInclusion (NonUnital.bComplex k A)
      (NonUnital.connesBoundaryHomotopy k A)
      (fun n => by simpa only [NonUnital.connesBoundaryHomotopy_hom] using
        NonUnital.connesBoundary_square k A n)) 1 ≫
          (NonUnital.mixedCyclicHomologyIso k A 1).hom

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
The Hochschild-to-cyclic chain inclusion factors as the inclusion
of column zero into the Connes mixed total followed by the mixed-to-
cyclic chain comparison. -/
lemma regularCyclicChainMap_eq :
    regularCyclicChainMap k A =
      ChainComplex.mixedColumnZeroInclusion (NonUnital.bComplex k A)
        (NonUnital.connesBoundaryHomotopy k A)
        (fun n => by simpa only [NonUnital.connesBoundaryHomotopy_hom] using
          NonUnital.connesBoundary_square k A n) ≫ NonUnital.mixedToCyclic k A := by
  let K := NonUnital.bComplex k A
  let H := NonUnital.connesBoundaryHomotopy k A
  let hSquare : ∀ n, H.hom n (n + 1) ≫ H.hom (n + 1) (n + 2) = 0 := fun n => by
    change (NonUnital.connesBoundaryHomotopy k A).hom n (n + 1) ≫
      (NonUnital.connesBoundaryHomotopy k A).hom (n + 1) (n + 2) = 0
    erw [NonUnital.connesBoundaryHomotopy_hom, NonUnital.connesBoundaryHomotopy_hom]
    exact NonUnital.connesBoundary_square k A n
  apply HomologicalComplex.hom_ext
  intro n
  change (regularCyclicChainMap k A).f n =
    (ChainComplex.mixedColumnZeroInclusion K H hSquare).f n ≫
      (NonUnital.mixedToCyclic k A).f n
  rw [regularCyclicChainMap_f, ChainComplex.mixedColumnZeroInclusion_f]
  change (NonUnital.cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) 0 n n
      (Nat.zero_add n) =
    NonUnital.mixedLevelInclusion k A 0 n n (by omega) ≫
      (NonUnital.mixedToCyclic k A).f n
  exact (NonUnital.mixedToCyclic_ι_zero k A n).symm

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
The map I_* : HH_1(A/k) → HC_1(A/k) is H_1(I), where
I is the first-column Hochschild-to-cyclic chain inclusion. -/
lemma regularCyclicOneMap_eq_homologyMap :
    regularCyclicOneMap k A =
      HomologicalComplex.homologyMap (regularCyclicChainMap k A) 1 := by
  let K := NonUnital.bComplex k A
  let H := NonUnital.connesBoundaryHomotopy k A
  let hSquare : ∀ n, H.hom n (n + 1) ≫ H.hom (n + 1) (n + 2) = 0 := fun n => by
    change (NonUnital.connesBoundaryHomotopy k A).hom n (n + 1) ≫
      (NonUnital.connesBoundaryHomotopy k A).hom (n + 1) (n + 2) = 0
    erw [NonUnital.connesBoundaryHomotopy_hom, NonUnital.connesBoundaryHomotopy_hom]
    exact NonUnital.connesBoundary_square k A n
  let m : K ⟶ NonUnital.connesMixedTotal k A := ChainComplex.mixedColumnZeroInclusion K H hSquare
  let I : NonUnital.connesMixedTotal k A ⟶ NonUnital.cyclicTotal k A := NonUnital.mixedToCyclic k A
  have hChain : regularCyclicChainMap k A = m ≫ I := regularCyclicChainMap_eq k A
  have hIso : (NonUnital.mixedCyclicHomologyIso k A 1).hom =
      HomologicalComplex.homologyMap I 1 := NonUnital.mixedCyclicHomologyIso_hom k A 1
  change HomologicalComplex.homologyMap m 1 ≫
    (NonUnital.mixedCyclicHomologyIso k A 1).hom = _
  exact (congrArg (fun j : (NonUnital.connesMixedTotal k A).homology 1 ⟶
      NonUnital.cyclicHomology k A 1 => HomologicalComplex.homologyMap m 1 ≫ j) hIso).trans
    ((HomologicalComplex.homologyMap_comp m I 1).symm.trans
      (congrArg (fun j : K ⟶ NonUnital.cyclicTotal k A => HomologicalComplex.homologyMap j 1)
        hChain.symm))

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
Restricting the degree-one class map q_H : C_1 → HH_1(A/k)
to the cycle module gives the canonical projection
Z_1(C) → HH_1(A/k). -/
@[reassoc]
lemma iCycles_regularHomologyOneClass :
    (NonUnital.bComplex k A).iCycles 1 ≫ regularHomologyOneClass k A =
      (NonUnital.bComplex k A).homologyπ 1 := by
  let K := NonUnital.bComplex k A
  let P := K.sc' 2 1 0
  let hi : (ComplexShape.down ℕ).prev 1 = 2 :=
    (ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel 2 1 from rfl)
  let hk : (ComplexShape.down ℕ).next 1 = 0 :=
    (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)
  let e : K.homology 1 ≅ P.homology := K.homologyIsoSc' 2 1 0 hi hk
  let c : K.cycles 1 ≅ P.cycles := K.cyclesIsoSc' 2 1 0 hi hk
  let r : P.homology ≅ P.opcycles := P.asIsoHomologyι (regularBoundaryOne_eq_zero k A)
  have hCycle : c.hom ≫ P.iCycles = K.iCycles 1 :=
    K.cyclesIsoSc'_hom_iCycles 2 1 0 hi hk
  have hPi : K.homologyπ 1 ≫ e.hom = c.hom ≫ P.homologyπ :=
    K.π_homologyIsoSc'_hom 2 1 0 hi hk
  have hQuotient : P.iCycles ≫ P.pOpcycles ≫ r.inv = P.homologyπ := by
    apply (cancel_mono P.homologyι).1
    have hCancel : r.inv ≫ P.homologyι = 𝟙 P.opcycles :=
      P.asIsoHomologyι_inv_comp_homologyι (regularBoundaryOne_eq_zero k A)
    calc
      (P.iCycles ≫ P.pOpcycles ≫ r.inv) ≫ P.homologyι =
          P.iCycles ≫ P.pOpcycles ≫ (r.inv ≫ P.homologyι) := by
        simp only [Category.assoc]
      _ = P.iCycles ≫ P.pOpcycles := by rw [hCancel, Category.comp_id]
      _ = P.homologyπ ≫ P.homologyι := P.homology_π_ι.symm
  change K.iCycles 1 ≫ (P.pOpcycles ≫ r.inv ≫ e.inv) = K.homologyπ 1
  calc
    K.iCycles 1 ≫ (P.pOpcycles ≫ r.inv ≫ e.inv) =
        (c.hom ≫ P.iCycles) ≫ (P.pOpcycles ≫ r.inv ≫ e.inv) :=
      congrArg (fun i => i ≫ (P.pOpcycles ≫ r.inv ≫ e.inv)) hCycle.symm
    _ = c.hom ≫ (P.iCycles ≫ P.pOpcycles ≫ r.inv) ≫ e.inv := by
      simp only [Category.assoc]
    _ = c.hom ≫ P.homologyπ ≫ e.inv :=
      congrArg (fun q => c.hom ≫ q ≫ e.inv) hQuotient
    _ = (K.homologyπ 1 ≫ e.hom) ≫ e.inv :=
      (Category.assoc c.hom P.homologyπ e.inv).symm.trans
        (congrArg (fun q => q ≫ e.inv) hPi.symm)
    _ = K.homologyπ 1 :=
      (Category.assoc (K.homologyπ 1) e.hom e.inv).trans
        ((congrArg (fun q => K.homologyπ 1 ≫ q) e.hom_inv_id).trans
          (Category.comp_id (K.homologyπ 1)))

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
The degree-one class maps satisfy I_* q_H = q_A, where
q_A : C_1 → HC_1(A/k) is the cyclic tensor-class map. -/
@[reassoc]
lemma regularHomologyOneClass_comp_regularCyclicOneMap :
    regularHomologyOneClass k A ≫ regularCyclicOneMap k A = cyclicOneClass k A := by
  let K := NonUnital.bComplex k A
  let H := NonUnital.connesBoundaryHomotopy k A
  let hSquare : ∀ n, H.hom n (n + 1) ≫ H.hom (n + 1) (n + 2) = 0 := fun n => by
    change (NonUnital.connesBoundaryHomotopy k A).hom n (n + 1) ≫
      (NonUnital.connesBoundaryHomotopy k A).hom (n + 1) (n + 2) = 0
    erw [NonUnital.connesBoundaryHomotopy_hom, NonUnital.connesBoundaryHomotopy_hom]
    exact NonUnital.connesBoundary_square k A n
  let P := K.sc' 2 1 0
  let Q := ChainComplex.mixedHomologyOneShortComplex K H
  let m : K ⟶ NonUnital.connesMixedTotal k A :=
    ChainComplex.mixedColumnZeroInclusion K H hSquare
  let eK : K.homology 1 ≅ P.homology := K.homologyIsoSc' 2 1 0
    ((ComplexShape.down ℕ).prev_eq' (by show (ComplexShape.down ℕ).Rel 2 1; rfl))
    ((ComplexShape.down ℕ).next_eq' (by show (ComplexShape.down ℕ).Rel 1 0; rfl))
  let eM : (NonUnital.connesMixedTotal k A).homology 1 ≅ Q.homology :=
    connesMixedOnePresentationIso k A
  let φ : P ⟶ Q := ChainComplex.mixedColumnZeroShortComplexMap K H
  let qP : K.X 1 ⟶ P.homology :=
    P.pOpcycles ≫ (P.asIsoHomologyι (regularBoundaryOne_eq_zero k A)).inv
  let qQ : K.X 1 ⟶ Q.homology :=
    Q.pOpcycles ≫ (Q.asIsoHomologyι (regularBoundaryOne_eq_zero k A)).inv
  have hM : HomologicalComplex.homologyMap m 1 ≫ eM.hom =
      eK.hom ≫ ShortComplex.homologyMap φ :=
    ChainComplex.mixedColumnZeroInclusion_homology K H hSquare
  have hQ : qP ≫ ShortComplex.homologyMap φ = qQ :=
    ChainComplex.mixedColumnZeroShortComplexMap_quotient K H
      (regularBoundaryOne_eq_zero k A)
  have hA : regularHomologyOneClass k A ≫ HomologicalComplex.homologyMap m 1 ≫
      eM.hom = qQ := by
    change (qP ≫ eK.inv) ≫ (HomologicalComplex.homologyMap m 1 ≫ eM.hom) = qQ
    rw [hM]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact hQ
  have hB : regularHomologyOneClass k A ≫ HomologicalComplex.homologyMap m 1 =
      qQ ≫ eM.inv := by
    apply (cancel_mono eM.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hA
  change regularHomologyOneClass k A ≫
      (HomologicalComplex.homologyMap m 1 ≫ (NonUnital.mixedCyclicHomologyIso k A 1).hom) =
    qQ ≫ eM.inv ≫ (NonUnital.mixedCyclicHomologyIso k A 1).hom
  exact (Category.assoc (regularHomologyOneClass k A)
      (HomologicalComplex.homologyMap m 1) (NonUnital.mixedCyclicHomologyIso k A 1).hom).symm.trans
    ((congrArg (fun f => f ≫ (NonUnital.mixedCyclicHomologyIso k A 1).hom) hB).trans
      (Category.assoc qQ eM.inv (NonUnital.mixedCyclicHomologyIso k A 1).hom))

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
The degree-one first-column map I_1 : C_1 → T_1 has cycle
values: d_T I_1 = 0, because the regular Hochschild boundary
b_1 is zero. -/
lemma regularCyclicChainMap_f_one_closed :
    (regularCyclicChainMap k A).f 1 ≫ (NonUnital.cyclicTotal k A).d 1 0 = 0 :=
  ((regularCyclicChainMap k A).comm 1 0).trans
    ((congrArg (fun d => d ≫ (regularCyclicChainMap k A).f 0)
      (regularBoundaryOne_eq_zero k A)).trans
        (Limits.zero_comp (f := (regularCyclicChainMap k A).f 0)))

/-- Let k be a commutative ring and A a commutative unital k-algebra.
Put C_n = A ⊗[k] A^{⊗n}, Ω_A = Ω_{A/k}, and let
d_A : A → Ω_A be the universal k-derivation.
The cyclic tensor-class map q_A : C_1 → HC_1(A/k) is
obtained by lifting I_1 to the cycle module Z_1(T) and then
projecting to H_1(T). -/
lemma cyclicOneClass_eq_liftCycles :
    cyclicOneClass k A =
      (NonUnital.cyclicTotal k A).liftCycles ((regularCyclicChainMap k A).f 1) 0
        ((ComplexShape.down ℕ).next_eq'
          (show (ComplexShape.down ℕ).Rel 1 0 from rfl))
        (regularCyclicChainMap_f_one_closed k A) ≫
          (NonUnital.cyclicTotal k A).homologyπ 1 := by
  let K := NonUnital.bComplex k A
  let T := NonUnital.cyclicTotal k A
  let j : K ⟶ T := regularCyclicChainMap k A
  let hk : (ComplexShape.down ℕ).next 1 = 0 :=
    (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)
  let δ : K.X 1 ⟶ T.cycles 1 :=
    T.liftCycles (j.f 1) 0 hk (regularCyclicChainMap_f_one_closed k A)
  have hδ : δ ≫ T.iCycles 1 = j.f 1 :=
    T.liftCycles_i (j.f 1) 0 hk (regularCyclicChainMap_f_one_closed k A)
  have hCycles : K.iCycles 1 ≫ δ = HomologicalComplex.cyclesMap j 1 := by
    apply (cancel_mono (T.iCycles 1)).1
    exact (Category.assoc (K.iCycles 1) δ (T.iCycles 1)).trans
      ((congrArg (fun d => K.iCycles 1 ≫ d) hδ).trans
        (HomologicalComplex.cyclesMap_i j 1).symm)
  have hClass : cyclicOneClass k A = regularHomologyOneClass k A ≫
      HomologicalComplex.homologyMap j 1 :=
    (regularHomologyOneClass_comp_regularCyclicOneMap k A).symm.trans
      (congrArg (fun m => regularHomologyOneClass k A ≫ m)
        (regularCyclicOneMap_eq_homologyMap k A))
  letI : IsIso (K.iCycles 1) :=
    K.isIso_iCycles 1 0 hk (regularBoundaryOne_eq_zero k A)
  apply (cancel_epi (K.iCycles 1)).1
  change K.iCycles 1 ≫ cyclicOneClass k A = K.iCycles 1 ≫ δ ≫ T.homologyπ 1
  have hFirst : K.iCycles 1 ≫ cyclicOneClass k A =
      K.homologyπ 1 ≫ HomologicalComplex.homologyMap j 1 :=
    (congrArg (fun q : K.X 1 ⟶ T.homology 1 => K.iCycles 1 ≫ q) hClass).trans
      ((Category.assoc (K.iCycles 1) (regularHomologyOneClass k A)
        (HomologicalComplex.homologyMap j 1)).symm.trans
          (congrArg (fun q : K.cycles 1 ⟶ K.homology 1 => q ≫ HomologicalComplex.homologyMap j 1)
            (iCycles_regularHomologyOneClass k A)))
  have hLast : HomologicalComplex.cyclesMap j 1 ≫ T.homologyπ 1 =
      K.iCycles 1 ≫ δ ≫ T.homologyπ 1 :=
    (congrArg (fun q : K.cycles 1 ⟶ T.cycles 1 => q ≫ T.homologyπ 1) hCycles.symm).trans
      (Category.assoc (K.iCycles 1) δ (T.homologyπ 1))
  exact hFirst.trans ((HomologicalComplex.homologyπ_naturality j 1).trans hLast)

private lemma regularCyclicChainMapLift_f_one_closed.{xCC, uCC, vCC}
    (k : Type uCC) [CommRing k] (A : Type vCC) [CommRing A] [Algebra k A] :
    (regularCyclicChainMapLift.{xCC} k A).f 1 ≫
      (HomologicalComplex₂.total ((((ModuleCat.uliftFunctor.{xCC, max uCC vCC} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (NonUnital.cyclicBicomplex k A)) (ComplexShape.down ℕ)).d 1 0 = 0 := by
  let U := ModuleCat.uliftFunctor.{xCC, max uCC vCC} k
  let K := (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj (NonUnital.bComplex k A)
  let T : HomologicalComplex₂ (ModuleCat.{max xCC uCC vCC} k)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (NonUnital.cyclicBicomplex k A)
  let j : K ⟶ T.total (ComplexShape.down ℕ) := regularCyclicChainMapLift.{xCC} k A
  have hZero : K.d 1 0 = 0 := by
    change U.map ((NonUnital.bComplex k A).d 1 0) = 0
    rw [regularBoundaryOne_eq_zero, U.map_zero]
  exact (j.comm 1 0).trans
    ((congrArg (fun d => d ≫ j.f 0) hZero).trans (Limits.zero_comp (f := j.f 0)))

private lemma cyclicOneClass_lift_cycles.{xLC, uLC, vLC}
    (k : Type uLC) [CommRing k] (A : Type vLC) [CommRing A] [Algebra k A] :
    let U := ModuleCat.uliftFunctor.{xLC, max uLC vLC} k
    let L := HomologicalComplex₂.total (((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (NonUnital.cyclicBicomplex k A)) (ComplexShape.down ℕ)
    U.map (cyclicOneClass k A) ≫ (NonUnital.cyclicHomologyLiftIso.{xLC} k A 1).hom =
      L.liftCycles ((regularCyclicChainMapLift.{xLC} k A).f 1) 0
        ((ComplexShape.down ℕ).next_eq'
          (show (ComplexShape.down ℕ).Rel 1 0 from rfl))
        (regularCyclicChainMapLift_f_one_closed.{xLC} k A) ≫ L.homologyπ 1 := by
  let U := ModuleCat.uliftFunctor.{xLC, max uLC vLC} k
  let K := NonUnital.bComplex k A
  let T := NonUnital.cyclicTotal k A
  let UT := (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj T
  let L := HomologicalComplex₂.total (((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (NonUnital.cyclicBicomplex k A)) (ComplexShape.down ℕ)
  let j : K ⟶ T := regularCyclicChainMap k A
  let jL := regularCyclicChainMapLift.{xLC} k A
  let hk : (ComplexShape.down ℕ).next 1 = 0 :=
    (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)
  let δ : K.X 1 ⟶ T.cycles 1 :=
    T.liftCycles (j.f 1) 0 hk (regularCyclicChainMap_f_one_closed k A)
  let δL : U.obj (K.X 1) ⟶ L.cycles 1 :=
    L.liftCycles (jL.f 1) 0 hk (regularCyclicChainMapLift_f_one_closed.{xLC} k A)
  let e : UT ≅ L := NonUnital.cyclicTotalLiftIso.{xLC} k A
  let hH : UT.homology 1 ≅ U.obj (T.homology 1) := (T.sc 1).mapHomologyIso U
  let hC : UT.cycles 1 ≅ U.obj (T.cycles 1) := (T.sc 1).mapCyclesIso U
  have hPack : (NonUnital.cyclicHomologyLiftIso.{xLC} k A 1).hom =
      hH.inv ≫ HomologicalComplex.homologyMap e.hom 1 := rfl
  have hOriginal : cyclicOneClass k A = δ ≫ T.homologyπ 1 :=
    cyclicOneClass_eq_liftCycles k A
  have hPi : UT.homologyπ 1 ≫ hH.hom = hC.hom ≫ U.map (T.homologyπ 1) :=
    ShortComplex.homologyπ_comp_mapHomologyIso_hom (T.sc 1) U
  have hPiInv : U.map (T.homologyπ 1) ≫ hH.inv = hC.inv ≫ UT.homologyπ 1 := by
    apply (cancel_mono hH.hom).1
    have hLeft : (U.map (T.homologyπ 1) ≫ hH.inv) ≫ hH.hom =
        U.map (T.homologyπ 1) :=
      (Category.assoc (U.map (T.homologyπ 1)) hH.inv hH.hom).trans
        ((congrArg (fun m => U.map (T.homologyπ 1) ≫ m) hH.inv_hom_id).trans
          (Category.comp_id _))
    have hRight : (hC.inv ≫ UT.homologyπ 1) ≫ hH.hom =
        U.map (T.homologyπ 1) :=
      (Category.assoc hC.inv (UT.homologyπ 1) hH.hom).trans
        ((congrArg (fun m => hC.inv ≫ m) hPi).trans
          (hC.inv_hom_id_assoc (U.map (T.homologyπ 1))))
    exact hLeft.trans hRight.symm
  have hCycle : hC.inv ≫ UT.iCycles 1 = U.map (T.iCycles 1) :=
    (congrArg (fun m => hC.inv ≫ m)
      ((T.sc 1).mapCyclesIso_hom_iCycles U).symm).trans
        (hC.inv_hom_id_assoc (U.map (T.iCycles 1)))
  have hδ : δ ≫ T.iCycles 1 = j.f 1 :=
    T.liftCycles_i (j.f 1) 0 hk (regularCyclicChainMap_f_one_closed k A)
  have hδL : δL ≫ L.iCycles 1 = jL.f 1 :=
    L.liftCycles_i (jL.f 1) 0 hk (regularCyclicChainMapLift_f_one_closed.{xLC} k A)
  have hField : jL.f 1 = U.map (j.f 1) ≫ e.hom.f 1 := rfl
  have hCycleMap : U.map δ ≫ hC.inv ≫ HomologicalComplex.cyclesMap e.hom 1 = δL := by
    apply (cancel_mono (L.iCycles 1)).1
    calc
      (U.map δ ≫ hC.inv ≫ HomologicalComplex.cyclesMap e.hom 1) ≫ L.iCycles 1 =
          U.map δ ≫ hC.inv ≫ (HomologicalComplex.cyclesMap e.hom 1 ≫ L.iCycles 1) := by
        simp only [Category.assoc]
      _ = U.map δ ≫ hC.inv ≫ (UT.iCycles 1 ≫ e.hom.f 1) :=
        congrArg (fun m => U.map δ ≫ hC.inv ≫ m)
          (HomologicalComplex.cyclesMap_i e.hom 1)
      _ = U.map δ ≫ (hC.inv ≫ UT.iCycles 1) ≫ e.hom.f 1 := by
        simp only [Category.assoc]
      _ = U.map δ ≫ U.map (T.iCycles 1) ≫ e.hom.f 1 :=
        congrArg (fun m => U.map δ ≫ m ≫ e.hom.f 1) hCycle
      _ = U.map (δ ≫ T.iCycles 1) ≫ e.hom.f 1 :=
        (Category.assoc (U.map δ) (U.map (T.iCycles 1)) (e.hom.f 1)).symm.trans
          (congrArg (fun m => m ≫ e.hom.f 1) (U.map_comp δ (T.iCycles 1)).symm)
      _ = U.map (j.f 1) ≫ e.hom.f 1 :=
        congrArg (fun m => U.map m ≫ e.hom.f 1) hδ
      _ = jL.f 1 := hField.symm
      _ = δL ≫ L.iCycles 1 := hδL.symm
  change U.map (cyclicOneClass k A) ≫ (NonUnital.cyclicHomologyLiftIso.{xLC} k A 1).hom =
    δL ≫ L.homologyπ 1
  calc
    U.map (cyclicOneClass k A) ≫ (NonUnital.cyclicHomologyLiftIso.{xLC} k A 1).hom =
        U.map (δ ≫ T.homologyπ 1) ≫ (hH.inv ≫ HomologicalComplex.homologyMap e.hom 1) :=
      congrArg₂ (fun a b => a ≫ b) (congrArg U.map hOriginal) hPack
    _ = U.map δ ≫ U.map (T.homologyπ 1) ≫ hH.inv ≫
        HomologicalComplex.homologyMap e.hom 1 := by
      rw [U.map_comp]
      simp only [Category.assoc]
    _ = U.map δ ≫ (hC.inv ≫ UT.homologyπ 1) ≫
        HomologicalComplex.homologyMap e.hom 1 :=
      congrArg (fun m => U.map δ ≫ m ≫ HomologicalComplex.homologyMap e.hom 1) hPiInv
    _ = U.map δ ≫ hC.inv ≫ (UT.homologyπ 1 ≫
        HomologicalComplex.homologyMap e.hom 1) := by
      simp only [Category.assoc]
    _ = U.map δ ≫ hC.inv ≫ (HomologicalComplex.cyclesMap e.hom 1 ≫ L.homologyπ 1) :=
      congrArg (fun m => U.map δ ≫ hC.inv ≫ m)
        (HomologicalComplex.homologyπ_naturality e.hom 1)
    _ = (U.map δ ≫ hC.inv ≫ HomologicalComplex.cyclesMap e.hom 1) ≫ L.homologyπ 1 := by
      simp only [Category.assoc]
    _ = δL ≫ L.homologyπ 1 :=
      congrArg (fun m => m ≫ L.homologyπ 1) hCycleMap

end Commutative

section AlgebraMaps

variable {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]
  {B : Type w} [CommRing B] [Algebra k B]

/-- Let k be commutative, A,B commutative unital k-algebras in
independent carrier universes, and f : A → B a unital k-algebra
homomorphism. Write Ω_A = Ω_{A/k}, Ω_B = Ω_{B/k}, and
Q_A = Ω_A / Im_k(d_A), Q_B = Ω_B / Im_k(d_B).
The induced k-linear map κ_f : Ω_A → Ω_B sends d_A a to
d_B(f(a)). It is also f-semilinear for the algebra actions. -/
def kaehlerMap (f : A →ₐ[k] B) : KaehlerDifferential k A →ₗ[k] KaehlerDifferential k B := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algHom f
  exact (KaehlerDifferential.map k k A B).restrictScalars k

/-- Let k be commutative, A,B commutative unital k-algebras in
independent carrier universes, and f : A → B a unital k-algebra
homomorphism. Write Ω_A = Ω_{A/k}, Ω_B = Ω_{B/k}, and
Q_A = Ω_A / Im_k(d_A), Q_B = Ω_B / Im_k(d_B).
The universal-differential map satisfies
κ_f(d_A a) = d_B(f(a)) for every a ∈ A. -/
lemma kaehlerMap_D (f : A →ₐ[k] B) (a : A) :
    kaehlerMap f (KaehlerDifferential.D k A a) = KaehlerDifferential.D k B (f a) := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algHom f
  exact KaehlerDifferential.map_D k k A B a

/-- Let k be commutative, A,B commutative unital k-algebras in
independent carrier universes, and f : A → B a unital k-algebra
homomorphism. Write Ω_A = Ω_{A/k}, Ω_B = Ω_{B/k}, and
Q_A = Ω_A / Im_k(d_A), Q_B = Ω_B / Im_k(d_B).
The map κ_f : Ω_A → Ω_B satisfies the algebra scalar law
κ_f(aω) = f(a)κ_f(ω), while its ground action remains k-linear. -/
lemma kaehlerMap_smul (f : A →ₐ[k] B) (a : A) (ω : KaehlerDifferential k A) :
    kaehlerMap f (a • ω) = f a • kaehlerMap f ω := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algHom f
  have h := (KaehlerDifferential.map k k A B).map_smul a ω
  exact h.trans (IsScalarTower.algebraMap_smul B a
    (KaehlerDifferential.map k k A B ω)).symm

/-- Let k be commutative, A,B commutative unital k-algebras in
independent carrier universes, and f : A → B a unital k-algebra
homomorphism. Write Ω_A = Ω_{A/k}, Ω_B = Ω_{B/k}, and
Q_A = Ω_A / Im_k(d_A), Q_B = Ω_B / Im_k(d_B).
The map κ_f carries Im_k(d_A) into Im_k(d_B), so it induces
a k-linear map Q(f) : Q_A → Q_B on exact-differential quotients. -/
def kaehlerExactMap (f : A →ₐ[k] B) : KaehlerExactQuotient k A →ₗ[k]
    KaehlerExactQuotient k B :=
  (LinearMap.range (KaehlerDifferential.D k A).toLinearMap).liftQ
    ((kaehlerClass k B).comp (kaehlerMap f)) (by
      intro ω hω
      obtain ⟨a, rfl⟩ := hω
      change kaehlerClass k B (kaehlerMap f (KaehlerDifferential.D k A a)) = 0
      rw [kaehlerMap_D, kaehlerClass, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨f a, rfl⟩)

/-- Let k be commutative, A,B commutative unital k-algebras in
independent carrier universes, and f : A → B a unital k-algebra
homomorphism. Write Ω_A = Ω_{A/k}, Ω_B = Ω_{B/k}, and
Q_A = Ω_A / Im_k(d_A), Q_B = Ω_B / Im_k(d_B).
On a form representative ω ∈ Ω_A, the quotient map has value
Q(f)([ω]) = [κ_f(ω)]. -/
lemma kaehlerExactMap_class (f : A →ₐ[k] B) (ω : KaehlerDifferential k A) :
    kaehlerExactMap f (kaehlerClass k A ω) = kaehlerClass k B (kaehlerMap f ω) := rfl

/-- Let k be commutative, A,B commutative unital k-algebras in
independent carrier universes, and f : A → B a unital k-algebra
homomorphism. Write Ω_A = Ω_{A/k}, Ω_B = Ω_{B/k}, and
Q_A = Ω_A / Im_k(d_A), Q_B = Ω_B / Im_k(d_B).
The tensor representatives satisfy
Q(f) τ_A = τ_B (f ⊗_k f)
in degree-one coordinates. Each coefficient and tail factor is mapped
by the same algebra homomorphism. -/
lemma cyclicOneRepresentative_naturality (f : A →ₐ[k] B) :
    (kaehlerExactMap f).comp (cyclicOneRepresentative k A) =
      (cyclicOneRepresentative k B).comp (TensorPower.consLevelMap f.toLinearMap 1) := by
  apply tensorPower_ext
  intro a s
  change kaehlerExactMap f (cyclicOneRepresentative k A
      (a ⊗ₜ[k] PiTensorProduct.tprod k s)) =
    cyclicOneRepresentative k B
      (TensorPower.consLevelMap f.toLinearMap 1 (a ⊗ₜ[k] PiTensorProduct.tprod k s))
  rw [cyclicOneRepresentative_tprod, kaehlerExactMap_class, kaehlerMap_smul, kaehlerMap_D]
  simp only [TensorPower.consLevelMap, TensorProduct.map_tmul, PiTensorProduct.map_tprod,
    cyclicOneRepresentative_tprod]
  rfl

/-- Let k be commutative and A,B commutative unital k-algebras in
independent carrier universes. For a multiplicative k-linear map
f : A → B, the cyclic degree-one class maps satisfy
HC_1(f) q_A = q_B (f ⊗_k f).
This equality concerns the first-column tensor classes and does not
require preservation of the unit by f. -/
lemma cyclicOneClass_naturality (f : A →ₙₐ[k] B) :
    (NonUnital.cyclicHomologyLinearMap f 1).comp (cyclicOneClass k A).hom =
      (cyclicOneClass k B).hom.comp (TensorPower.consLevelMap (f : A →ₗ[k] B) 1) := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let KA := (UA.mapHomologicalComplex (ComplexShape.down ℕ)).obj (NonUnital.bComplex k A)
  let KB := (UB.mapHomologicalComplex (ComplexShape.down ℕ)).obj (NonUnital.bComplex k B)
  let TA := HomologicalComplex₂.total (((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (NonUnital.cyclicBicomplex k A)) (ComplexShape.down ℕ)
  let TB := HomologicalComplex₂.total (((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (NonUnital.cyclicBicomplex k B)) (ComplexShape.down ℕ)
  let jA : KA ⟶ TA := regularCyclicChainMapLift.{w} k A
  let jB : KB ⟶ TB := regularCyclicChainMapLift.{v} k B
  let m : KA ⟶ KB := (NonUnital.cyclicBicomplexMap f).f 0
  let c : TA ⟶ TB := HomologicalComplex₂.total.map (NonUnital.cyclicBicomplexMap f)
    (ComplexShape.down ℕ)
  let eA : UA.obj (NonUnital.cyclicHomology k A 1) ≅ TA.homology 1 :=
    NonUnital.cyclicHomologyLiftIso.{w} k A 1
  let eB : UB.obj (NonUnital.cyclicHomology k B 1) ≅ TB.homology 1 :=
    NonUnital.cyclicHomologyLiftIso.{v} k B 1
  let hk : (ComplexShape.down ℕ).next 1 = 0 :=
    (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)
  let δA : KA.X 1 ⟶ TA.cycles 1 :=
    TA.liftCycles (jA.f 1) 0 hk (regularCyclicChainMapLift_f_one_closed.{w} k A)
  let δB : KB.X 1 ⟶ TB.cycles 1 :=
    TB.liftCycles (jB.f 1) 0 hk (regularCyclicChainMapLift_f_one_closed.{v} k B)
  have hA : UA.map (cyclicOneClass k A) ≫ eA.hom = δA ≫ TA.homologyπ 1 :=
    cyclicOneClass_lift_cycles.{w} k A
  have hB : UB.map (cyclicOneClass k B) ≫ eB.hom = δB ≫ TB.homologyπ 1 :=
    cyclicOneClass_lift_cycles.{v} k B
  have hJ : jA ≫ c = m ≫ jB := regularCyclicChainMapLift_naturality f
  have hField : jA.f 1 ≫ c.f 1 = m.f 1 ≫ jB.f 1 :=
    congrArg (fun j : KA ⟶ TB => j.f 1) hJ
  have hδA : δA ≫ TA.iCycles 1 = jA.f 1 :=
    TA.liftCycles_i (jA.f 1) 0 hk (regularCyclicChainMapLift_f_one_closed.{w} k A)
  have hδB : δB ≫ TB.iCycles 1 = jB.f 1 :=
    TB.liftCycles_i (jB.f 1) 0 hk (regularCyclicChainMapLift_f_one_closed.{v} k B)
  have hCycle : δA ≫ HomologicalComplex.cyclesMap c 1 = m.f 1 ≫ δB := by
    apply (cancel_mono (TB.iCycles 1)).1
    calc
      (δA ≫ HomologicalComplex.cyclesMap c 1) ≫ TB.iCycles 1 =
          δA ≫ (HomologicalComplex.cyclesMap c 1 ≫ TB.iCycles 1) :=
        Category.assoc δA (HomologicalComplex.cyclesMap c 1) (TB.iCycles 1)
      _ = δA ≫ (TA.iCycles 1 ≫ c.f 1) :=
        congrArg (fun i => δA ≫ i) (HomologicalComplex.cyclesMap_i c 1)
      _ = (δA ≫ TA.iCycles 1) ≫ c.f 1 :=
        (Category.assoc δA (TA.iCycles 1) (c.f 1)).symm
      _ = jA.f 1 ≫ c.f 1 := congrArg (fun j => j ≫ c.f 1) hδA
      _ = m.f 1 ≫ jB.f 1 := hField
      _ = m.f 1 ≫ (δB ≫ TB.iCycles 1) := congrArg (fun j => m.f 1 ≫ j) hδB.symm
      _ = (m.f 1 ≫ δB) ≫ TB.iCycles 1 :=
        (Category.assoc (m.f 1) δB (TB.iCycles 1)).symm
  have hLift : (UA.map (cyclicOneClass k A) ≫ eA.hom) ≫
      HomologicalComplex.homologyMap c 1 = m.f 1 ≫ (UB.map (cyclicOneClass k B) ≫ eB.hom) := by
    calc
      (UA.map (cyclicOneClass k A) ≫ eA.hom) ≫ HomologicalComplex.homologyMap c 1 =
          (δA ≫ TA.homologyπ 1) ≫ HomologicalComplex.homologyMap c 1 :=
        congrArg (fun q => q ≫ HomologicalComplex.homologyMap c 1) hA
      _ = δA ≫ (TA.homologyπ 1 ≫ HomologicalComplex.homologyMap c 1) :=
        Category.assoc δA (TA.homologyπ 1) (HomologicalComplex.homologyMap c 1)
      _ = δA ≫ (HomologicalComplex.cyclesMap c 1 ≫ TB.homologyπ 1) :=
        congrArg (fun q => δA ≫ q) (HomologicalComplex.homologyπ_naturality c 1)
      _ = (δA ≫ HomologicalComplex.cyclesMap c 1) ≫ TB.homologyπ 1 :=
        (Category.assoc δA (HomologicalComplex.cyclesMap c 1) (TB.homologyπ 1)).symm
      _ = (m.f 1 ≫ δB) ≫ TB.homologyπ 1 := congrArg (fun q => q ≫ TB.homologyπ 1) hCycle
      _ = m.f 1 ≫ (UB.map (cyclicOneClass k B) ≫ eB.hom) :=
        (Category.assoc (m.f 1) δB (TB.homologyπ 1)).trans
          (congrArg (fun q => m.f 1 ≫ q) hB.symm)
  apply LinearMap.ext
  intro x
  have hEval := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hLift) (ULift.up x)
  have hLevel : m.f 1 = NonUnital.levelMapLift (f : A →ₗ[k] B) 1 :=
    NonUnital.cyclicBicomplexMap_f_f f 0 1
  rw [hLevel] at hEval
  have hValue : HomologicalComplex.homologyMap c 1
      (eA.hom (ULift.up ((cyclicOneClass k A).hom x))) =
        eB.hom (ULift.up ((cyclicOneClass k B).hom
          (TensorPower.consLevelMap (f : A →ₗ[k] B) 1 x))) := by
    change HomologicalComplex.homologyMap c 1
      (eA.hom (ULift.up ((cyclicOneClass k A).hom x))) =
        eB.hom (ULift.up ((cyclicOneClass k B).hom
          (TensorPower.consLevelMap (f : A →ₗ[k] B) 1 x))) at hEval
    exact hEval
  have hNative : eB.hom (ULift.up
      (NonUnital.cyclicHomologyLinearMap f 1 ((cyclicOneClass k A).hom x))) =
        HomologicalComplex.homologyMap c 1
          (eA.hom (ULift.up ((cyclicOneClass k A).hom x))) :=
    NonUnital.cyclicHomologyLinearMap_lift f 1 ((cyclicOneClass k A).hom x)
  have hOriginal := eB.toLinearEquiv.injective (hNative.trans hValue)
  exact congrArg ULift.down hOriginal

/-- Let k be commutative, A,B commutative unital k-algebras in
independent carrier universes, and f : A → B a unital k-algebra
homomorphism. Write Ω_A = Ω_{A/k}, Ω_B = Ω_{B/k}, and
Q_A = Ω_A / Im_k(d_A), Q_B = Ω_B / Im_k(d_B).
The cyclic homology equivalences are natural:
Q(f) E_A = E_B HC_1(f), as k-linear maps HC_1(A/k) → Q_B. -/
lemma cyclicHomologyOneLinearEquiv_naturality (f : A →ₐ[k] B) :
    (kaehlerExactMap f).comp (cyclicHomologyOneLinearEquiv k A).toLinearMap =
      (cyclicHomologyOneLinearEquiv k B).toLinearMap.comp
        (NonUnital.cyclicHomologyLinearMap f.toNonUnitalAlgHom 1) := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ :=
    ((ModuleCat.epi_iff_surjective (cyclicOneClass k A)).mp inferInstance) z
  have hA : (cyclicHomologyOneLinearEquiv k A) ((cyclicOneClass k A).hom x) =
      cyclicOneRepresentative k A x :=
    cyclicOneClass_linearEquiv k A x
  have hB : (cyclicHomologyOneLinearEquiv k B)
      ((cyclicOneClass k B).hom (TensorPower.consLevelMap f.toLinearMap 1 x)) =
        cyclicOneRepresentative k B (TensorPower.consLevelMap f.toLinearMap 1 x) :=
    cyclicOneClass_linearEquiv k B _
  have hMap : NonUnital.cyclicHomologyLinearMap f.toNonUnitalAlgHom 1
      ((cyclicOneClass k A).hom x) =
        (cyclicOneClass k B).hom (TensorPower.consLevelMap f.toLinearMap 1 x) :=
    LinearMap.congr_fun (cyclicOneClass_naturality f.toNonUnitalAlgHom) x
  change kaehlerExactMap f ((cyclicHomologyOneLinearEquiv k A) ((cyclicOneClass k A).hom x)) =
    (cyclicHomologyOneLinearEquiv k B)
      (NonUnital.cyclicHomologyLinearMap f.toNonUnitalAlgHom 1 ((cyclicOneClass k A).hom x))
  calc
    kaehlerExactMap f ((cyclicHomologyOneLinearEquiv k A) ((cyclicOneClass k A).hom x)) =
        kaehlerExactMap f (cyclicOneRepresentative k A x) := congrArg (kaehlerExactMap f) hA
    _ = cyclicOneRepresentative k B (TensorPower.consLevelMap f.toLinearMap 1 x) :=
      LinearMap.congr_fun (cyclicOneRepresentative_naturality f) x
    _ = (cyclicHomologyOneLinearEquiv k B)
        ((cyclicOneClass k B).hom (TensorPower.consLevelMap f.toLinearMap 1 x)) := hB.symm
    _ = (cyclicHomologyOneLinearEquiv k B)
        (NonUnital.cyclicHomologyLinearMap f.toNonUnitalAlgHom 1 ((cyclicOneClass k A).hom x)) :=
      congrArg (cyclicHomologyOneLinearEquiv k B) hMap.symm

/-- Let k be commutative, A,B commutative unital k-algebras in
independent carrier universes, and f : A → B a unital k-algebra
homomorphism. Write Ω_A = Ω_{A/k}, Ω_B = Ω_{B/k}, and
Q_A = Ω_A / Im_k(d_A), Q_B = Ω_B / Im_k(d_B).
The inverse equivalences satisfy
HC_1(f) E_A⁻¹ = E_B⁻¹ Q(f), as k-linear maps Q_A → HC_1(B/k). -/
lemma cyclicHomologyOneLinearEquiv_inv_naturality (f : A →ₐ[k] B) :
    (NonUnital.cyclicHomologyLinearMap f.toNonUnitalAlgHom 1).comp
        (cyclicHomologyOneLinearEquiv k A).symm.toLinearMap =
      (cyclicHomologyOneLinearEquiv k B).symm.toLinearMap.comp (kaehlerExactMap f) := by
  apply LinearMap.ext
  intro ω
  apply (cyclicHomologyOneLinearEquiv k B).injective
  change (cyclicHomologyOneLinearEquiv k B)
      (NonUnital.cyclicHomologyLinearMap f.toNonUnitalAlgHom 1
        ((cyclicHomologyOneLinearEquiv k A).symm ω)) =
    (cyclicHomologyOneLinearEquiv k B)
      ((cyclicHomologyOneLinearEquiv k B).symm (kaehlerExactMap f ω))
  rw [LinearEquiv.apply_symm_apply]
  have h := LinearMap.congr_fun (cyclicHomologyOneLinearEquiv_naturality f)
    ((cyclicHomologyOneLinearEquiv k A).symm ω)
  change kaehlerExactMap f
      ((cyclicHomologyOneLinearEquiv k A) ((cyclicHomologyOneLinearEquiv k A).symm ω)) =
    (cyclicHomologyOneLinearEquiv k B)
      (NonUnital.cyclicHomologyLinearMap f.toNonUnitalAlgHom 1
        ((cyclicHomologyOneLinearEquiv k A).symm ω)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end AlgebraMaps

end ModuleCat.Algebra.Hochschild
