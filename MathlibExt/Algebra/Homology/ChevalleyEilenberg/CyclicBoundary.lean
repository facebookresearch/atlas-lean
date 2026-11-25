/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CyclicFirstFace
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraNaturality
public import MathlibExt.Algebra.Lie.OfNonUnitalAssociative

/-!
# Exterior-to-Connes chain maps

For a unital algebra over a commutative ring, the Connes boundary of full alternatization on n
+ 2 exterior inputs is n + 2 times the ordered tail product sum. When the ground ring is a
rational algebra, normalization by the number of inputs yields a chain map whose source
differential has the positive bracket convention.

Multiplying the map in degree n by `(-1)^n` gives the chain map from the positive tail of the
canonical Chevalley–Eilenberg complex. The constructions are natural under nonunital algebra
homomorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

local notation "Cλ" => ModuleCat.Algebra.Hochschild.NonUnital.connesComplex

/-- The integral full-permutation cyclic boundary is the source input count times the bracket-tail
sum. -/
theorem cyclicFullExterior_boundary_tail (n : ℕ) (a : Fin (n + 2) → A) :
    ((Cλ k A).d (n + 1) n).hom
        (cyclicFullExterior k A (n + 1) (exteriorPower.ιMulti k (n + 2) a)) =
      (n + 2) • cyclicTailProductUncurry k A n a := by
  rw [cyclicFullTensor_boundary_first, cyclicFullTensor_firstFace]

section Rational

variable [Algebra ℚ k]

/-- The positive CE boundary followed by the exterior map is the bracket-tail sum. -/
theorem cyclicExterior_positive_boundary (n : ℕ) (a : Fin (n + 2) → A) :
    cyclicExterior k A n
        (-differential k A (n + 1) (exteriorPower.ιMulti k (n + 2) a)) =
      cyclicTailProductUncurry k A n a := by
  rw [map_neg, differential_apply_ιMulti]
  unfold bracketBoundary
  rw [map_sum, ← Finset.sum_neg_distrib, cyclicTailProductUncurry_pure]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, cyclicExterior_pure]
  have hs (x : (Cλ k A).X n) :
      (-1 : k) ^ (i.val + j.val + 1) • x = (-1 : ℤ) ^ (i.val + j.val + 1) • x := by
    simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using
      Int.cast_smul_eq_zsmul k ((-1 : ℤ) ^ (i.val + j.val + 1)) x
  rw [hs, pow_succ, mul_neg_one, neg_smul, neg_neg]
  exact congrArg (fun b => (-1 : ℤ) ^ (i.val + j.val) • cyclicTailSum k A n b)
    (by
      funext t
      exact Fin.cases rfl (fun _ => rfl) t)

/-- The tail-normalized exterior map has the signed cyclic boundary law. -/
theorem cyclicExterior_boundary_pure (n : ℕ) (a : Fin (n + 2) → A) :
    ((Cλ k A).d (n + 1) n).hom
        (cyclicExterior k A (n + 1) (exteriorPower.ιMulti k (n + 2) a)) =
      cyclicExterior k A n
        (-differential k A (n + 1) (exteriorPower.ιMulti k (n + 2) a)) := by
  rw [cyclicExterior, LinearMap.smul_apply, map_smul,
    cyclicFullExterior_boundary_tail, cyclicExterior_positive_boundary]
  have hn : ((n + 2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  rw [← Nat.cast_smul_eq_nsmul k (n + 2), smul_smul,
    ← map_natCast (algebraMap ℚ k) (n + 2), ← map_mul,
    ← Nat.cast_succ, inv_mul_cancel₀ hn, map_one, one_smul]

/-- The whole exterior component commutes with the signed differential. -/
theorem cyclicExterior_boundary (n : ℕ) :
    (((Cλ k A).d (n + 1) n).hom).comp (cyclicExterior k A (n + 1)) =
      (cyclicExterior k A n).comp (-differential k A (n + 1)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change ((Cλ k A).d (n + 1) n).hom
      (cyclicExterior k A (n + 1) (exteriorPower.ιMulti k (n + 2) a)) =
    cyclicExterior k A n ((-differential k A (n + 1)) (exteriorPower.ιMulti k (n + 2) a))
  simpa only [LinearMap.neg_apply] using cyclicExterior_boundary_pure k A n a

/-- The shifted exterior complex with the positive bracket differential. -/
abbrev cyclicPrintedSource : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  ChainComplex.positiveTail (HomologicalComplex.negateDifferentials (canonicalChainData k A).complex)

/-- Normalized tail antisymmetrization as a chain map from the positive bracket convention to the
Connes complex. -/
def cyclicExteriorChainMap : cyclicPrintedSource k A ⟶ Cλ k A :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (cyclicExterior k A n)) (by
    intro n
    rw [ChainComplex.positiveTail_d_succ, HomologicalComplex.negateDifferentials_d]
    have hd : (((canonicalChainData k A).complex.d (n + 2) (n + 1)).hom :
        (⋀[k]^(n + 2) A) →ₗ[k] (⋀[k]^(n + 1) A)) = differential k A (n + 1) := by
      rw [ChainData.complex_d_succ]
      rfl
    apply ModuleCat.hom_ext
    change (((Cλ k A).d (n + 1) n).hom).comp (cyclicExterior k A (n + 1)) =
      (cyclicExterior k A n).comp
        (-((((canonicalChainData k A).complex).d (n + 2) (n + 1)).hom))
    rw [hd]
    exact cyclicExterior_boundary k A n)

/-- Its exact component is the exterior tail sum. -/
theorem cyclicExteriorChainMap_f (n : ℕ) :
    ((cyclicExteriorChainMap k A).f n).hom = cyclicExterior k A n := rfl

/-- The chain map from the positive Chevalley–Eilenberg tail whose component in degree n is
`(-1)^n` times normalized tail antisymmetrization. -/
def cyclicExteriorWeibelChainMap :
    ChainComplex.positiveTail (canonicalChainData k A).complex ⟶ Cλ k A :=
  ChainComplex.positiveTailMap (ChainComplex.negationIso (canonicalChainData k A).complex).hom ≫
    (-cyclicExteriorChainMap k A)

/-- Its component has exactly the source's `(-1)^n` multiplying the tail map. -/
theorem cyclicExteriorWeibelChainMap_f (n : ℕ) :
    ((cyclicExteriorWeibelChainMap k A).f n).hom = cyclicExteriorWeibel k A n := by
  let K := (canonicalChainData k A).complex
  let g : K.X (n + 1) ⟶ (Cλ k A).X n := -((cyclicExteriorChainMap k A).f n)
  have hg : (cyclicExteriorWeibelChainMap k A).f n =
      (ChainComplex.negationIso K).hom.f (n + 1) ≫ g := rfl
  have hsign : (ChainComplex.negationIso K).hom.f (n + 1) ≫ g =
      ChainComplex.degreeSign (n + 1) • g := by
    have hs : ((ChainComplex.negationIso K).hom.f (n + 1) : K.X (n + 1) ⟶ K.X (n + 1)) =
        ChainComplex.degreeSign (n + 1) • 𝟙 (K.X (n + 1)) :=
      ChainComplex.negationIso_hom_f K (n + 1)
    have hc : (ChainComplex.degreeSign (n + 1) • 𝟙 (K.X (n + 1))) ≫ g =
        ChainComplex.degreeSign (n + 1) • g := by
      rw [Preadditive.zsmul_comp, Category.id_comp]
    exact (congrArg (fun t : K.X (n + 1) ⟶ K.X (n + 1) => t ≫ g) hs).trans hc
  have h := congrArg ModuleCat.Hom.hom (hg.trans hsign)
  change ((cyclicExteriorWeibelChainMap k A).f n).hom =
    (ChainComplex.degreeSign (n + 1) • (-((cyclicExteriorChainMap k A).f n))).hom at h
  rw [ModuleCat.hom_zsmul, ModuleCat.hom_neg, cyclicExteriorChainMap_f] at h
  have hraw : (((cyclicExteriorWeibelChainMap k A).f n).hom :
      (⋀[k]^(n + 1) A) →ₗ[k] ((Cλ k A).X n)) =
      ChainComplex.degreeSign (n + 1) • (-cyclicExterior k A n) := h
  have hs : ChainComplex.degreeSign (n + 1) • (-cyclicExterior k A n) =
      cyclicExteriorWeibel k A n := by
    rw [smul_neg, cyclicExteriorWeibel]
    rw [ChainComplex.degreeSign_succ, neg_smul, neg_neg]
    simpa only [ChainComplex.degreeSign, Int.cast_pow, Int.cast_neg, Int.cast_one] using
      (Int.cast_smul_eq_zsmul k (ChainComplex.degreeSign n) (cyclicExterior k A n)).symm
  exact hraw.trans hs

/-- Degree zero is the one-factor Connes representative, with no degree sign. -/
theorem cyclicExteriorWeibelChainMap_zero_pure (x : A) :
    ((cyclicExteriorWeibelChainMap k A).f 0).hom
      (exteriorPower.ιMulti k 1 (fun _ => x)) =
      ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A 0
        (x ⊗ₜ[k] PiTensorProduct.tprod k (fun j : Fin 0 => j.elim0)) := by
  have hf := LinearMap.congr_fun (cyclicExteriorWeibelChainMap_f k A 0)
    (exteriorPower.ιMulti k 1 (fun _ => x))
  have hp := cyclicExteriorWeibel_pure k A 0 (fun _ => x)
  rw [pow_zero, one_smul, cyclicTailSum,
    Fintype.sum_subsingleton _ (1 : Equiv.Perm (Fin 0)), Equiv.Perm.sign_one, one_smul] at hp
  have htail : (fun _ : Fin 0 => x) = (fun j : Fin 0 => j.elim0) := by
    funext j
    exact j.elim0
  rw [htail] at hp
  exact hf.trans hp

/-- The printed-positive degree-one component sends the two-vector wedge to its ordered tensor
class. -/
theorem cyclicExteriorChainMap_one_pure (x y : A) :
    ((cyclicExteriorChainMap k A).f 1).hom (exteriorPower.ιMulti k 2 ![x, y]) =
      ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A 1
        (x ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => y)) := by
  have hf := LinearMap.congr_fun (cyclicExteriorChainMap_f k A 1)
    (exteriorPower.ιMulti k 2 ![x, y])
  have hp := cyclicExterior_pure k A 1 ![x, y]
  rw [cyclicTailSum, Fintype.sum_subsingleton _ (1 : Equiv.Perm (Fin 1)),
    Equiv.Perm.sign_one, one_smul] at hp
  simp only [Equiv.Perm.one_apply] at hp
  have htail : (fun j : Fin 1 => ![x, y] j.succ) = (fun _ : Fin 1 => y) := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  rw [htail] at hp
  exact hf.trans hp

/-- The positive degree-two bracket boundary is carried to the one-factor bracket class. -/
theorem cyclicExteriorChainMap_one_boundary (x y : A) :
    ((Cλ k A).d 1 0).hom
        (((cyclicExteriorChainMap k A).f 1).hom (exteriorPower.ιMulti k 2 ![x, y])) =
      ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A 0
        (⁅x, y⁆ ⊗ₜ[k] PiTensorProduct.tprod k (fun j : Fin 0 => j.elim0)) := by
  have hf := LinearMap.congr_fun (cyclicExteriorChainMap_f k A 1)
    (exteriorPower.ιMulti k 2 ![x, y])
  have hp : ((Cλ k A).d 1 0).hom
      (cyclicExterior k A 1 (exteriorPower.ιMulti k 2 ![x, y])) =
        ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A 0
          (⁅x, y⁆ ⊗ₜ[k] PiTensorProduct.tprod k (fun j : Fin 0 => j.elim0)) := by
    rw [cyclicExterior_boundary_pure, cyclicExterior_positive_boundary,
      cyclicTailProductUncurry_pure]
    have htail : (fun j : Fin 0 => (![] : Fin 0 → A) j) = (fun j : Fin 0 => j.elim0) := by
      funext j
      exact j.elim0
    rw [← htail]
    simp [cyclicTailSum]
  exact (congrArg ((Cλ k A).d 1 0).hom hf).trans hp

/-- The component in degree one is the negative of the ordered tensor representative. -/
theorem cyclicExteriorWeibelChainMap_one_pure (x y : A) :
    ((cyclicExteriorWeibelChainMap k A).f 1).hom (exteriorPower.ιMulti k 2 ![x, y]) =
      -ModuleCat.Algebra.Hochschild.Matrix.connesRepresentative k A 1
        (x ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => y)) := by
  have hf := LinearMap.congr_fun (cyclicExteriorWeibelChainMap_f k A 1)
    (exteriorPower.ιMulti k 2 ![x, y])
  have hp := cyclicExteriorWeibel_pure k A 1 ![x, y]
  rw [pow_one, neg_one_smul, cyclicTailSum,
    Fintype.sum_subsingleton _ (1 : Equiv.Perm (Fin 1)), Equiv.Perm.sign_one, one_smul] at hp
  simp only [Equiv.Perm.one_apply] at hp
  have htail : (fun j : Fin 1 => ![x, y] j.succ) = (fun _ : Fin 1 => y) := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  rw [htail] at hp
  exact hf.trans hp

section Naturality

variable {B : Type v} [Ring B] [Algebra k B]

/-- The CE positive-tail map induced by the noncommutative algebra map. -/
def cyclicWeibelSourceMap (f : A →ₙₐ[k] B) :
    ChainComplex.positiveTail (canonicalChainData k A).complex ⟶
      ChainComplex.positiveTail (canonicalChainData k B).complex :=
  ChainComplex.positiveTailMap (nativeComplexMap k A f.toLieHom)

/-- The printed-positive source map is the same map under differential negation. -/
def cyclicPrintedSourceMap (f : A →ₙₐ[k] B) : cyclicPrintedSource k A ⟶ cyclicPrintedSource k B :=
  ChainComplex.positiveTailMap (HomologicalComplex.negateMap (nativeComplexMap k A f.toLieHom))

/-- Positive-convention chain naturality uses the coefficient/exterior and Connes maps. -/
theorem cyclicExteriorChainMap_naturality (f : A →ₙₐ[k] B) :
    cyclicPrintedSourceMap k A f ≫ cyclicExteriorChainMap k B =
      cyclicExteriorChainMap k A ≫
        ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f := by
  apply HomologicalComplex.hom_ext
  intro n
  have hs : ((cyclicPrintedSourceMap k A f).f n).hom =
      exteriorPower.map (n + 1) (f : A →ₗ[k] B) := by
    change ((nativeComplexMap k A f.toLieHom).f (n + 1)).hom = _
    rw [nativeComplexMap_f]
    rfl
  apply ModuleCat.hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, ModuleCat.hom_comp,
    cyclicExteriorChainMap_f, cyclicExteriorChainMap_f, hs]
  change (cyclicExterior k B n).comp (exteriorPower.map (n + 1) (f : A →ₗ[k] B)) =
    (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f).f n).hom).comp
      (cyclicExterior k A n)
  exact (cyclicExterior_natural k A f n).symm

/-- The signed cyclic chain map is natural under nonunital coefficient algebra homomorphisms. -/
theorem cyclicExteriorWeibelChainMap_naturality (f : A →ₙₐ[k] B) :
    cyclicWeibelSourceMap k A f ≫ cyclicExteriorWeibelChainMap k B =
      cyclicExteriorWeibelChainMap k A ≫
        ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f := by
  apply HomologicalComplex.hom_ext
  intro n
  have hs : ((cyclicWeibelSourceMap k A f).f n).hom =
      exteriorPower.map (n + 1) (f : A →ₗ[k] B) := by
    change ((nativeComplexMap k A f.toLieHom).f (n + 1)).hom = _
    rw [nativeComplexMap_f]
    rfl
  apply ModuleCat.hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, ModuleCat.hom_comp,
    cyclicExteriorWeibelChainMap_f, cyclicExteriorWeibelChainMap_f, hs]
  change (cyclicExteriorWeibel k B n).comp (exteriorPower.map (n + 1) (f : A →ₗ[k] B)) =
    (((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f).f n).hom).comp
      (cyclicExteriorWeibel k A n)
  exact (cyclicExteriorWeibel_natural k A f n).symm

end Naturality

end Rational

end ChevalleyEilenberg

end
