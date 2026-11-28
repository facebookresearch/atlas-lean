/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# Precomposition and postcomposition of Hom cocycles

Let C be preadditive and n an integer. A degree-n Hom cocycle between integer cochain complexes
can be precomposed with a source complex map or postcomposed with a target complex map. These
actions obey identity, composition, zero and interchange laws.

For shifts a,m with m+a=0, the equivalence between maps K[a] → L and degree-m Hom cocycles is
natural for shifted source maps and target maps.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CochainComplex.HomComplex.Cocycle

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {F G H K L : CochainComplex C ℤ} {n : ℤ}

/-- Let C be a preadditive category and F,G,H,K,L be integer-indexed cochain complexes in C. For any
degree-n cocycle z from G to K, precomposition by id_G leaves z unchanged. -/
@[simp] theorem precomp_id (z : Cocycle G K n) : z.precomp (𝟙 G) = z := by
  apply Cocycle.ext
  simp

/-- Let C be a preadditive category and F,G,H,K,L be integer-indexed cochain complexes in C. For any
degree-n cocycle z from F to G, postcomposition by id_G leaves z unchanged. -/
@[simp] theorem postcomp_id (z : Cocycle F G n) : z.postcomp (𝟙 G) = z := by
  apply Cocycle.ext
  simp

/-- Let C be a preadditive category and F,G,H,K,L be integer-indexed cochain complexes in C. For z
from H to K of degree n and maps f : F → G, g : G → H, precomposing z by g ∘ f equals first
precomposing by g and then by f. -/
@[simp] theorem precomp_comp (z : Cocycle H K n) (f : F ⟶ G) (g : G ⟶ H) :
    z.precomp (f ≫ g) = (z.precomp g).precomp f := by
  apply Cocycle.ext
  simp

/-- Let C be a preadditive category and F,G,H,K,L be integer-indexed cochain complexes in C. For z
from F to G of degree n and maps f : G → K, g : K → L, postcomposing first by f and then by g
equals postcomposition by g ∘ f. -/
@[simp] theorem postcomp_comp (z : Cocycle F G n) (f : G ⟶ K) (g : K ⟶ L) :
    (z.postcomp f).postcomp g = z.postcomp (f ≫ g) := by
  apply Cocycle.ext
  simp

/-- Let C be a preadditive category and F,G,H,K,L be integer-indexed cochain complexes in C. For a
degree-n cocycle z from G to K, a source map f : F → G and target map g : K → L, precomposition
by f and postcomposition by g commute. -/
theorem precomp_postcomp (z : Cocycle G K n) (f : K ⟶ L) (g : F ⟶ G) :
    (z.postcomp f).precomp g = (z.precomp g).postcomp f := by
  apply Cocycle.ext
  simp

/-- Let C be a preadditive category and F,G,H,K,L be integer-indexed cochain complexes in C.
Precomposing a degree-n cocycle from G to K by the zero map F → G gives the zero degree-n
cocycle from F to K. -/
@[simp] theorem precomp_zero (z : Cocycle G K n) :
    z.precomp (0 : F ⟶ G) = 0 := by
  apply Cocycle.ext
  simp

/-- Let C be a preadditive category and F,G,H,K,L be integer-indexed cochain complexes in C.
Postcomposing a degree-n cocycle from F to G by the zero map G → K gives the zero degree-n
cocycle from F to K. -/
@[simp] theorem postcomp_zero (z : Cocycle F G n) :
    z.postcomp (0 : G ⟶ K) = 0 := by
  apply Cocycle.ext
  simp

/-- Let C be a preadditive category and F,G,H,K,L be integer-indexed cochain complexes in C. For a
target map f : G → K, postcomposition sends the zero degree-n cocycle from F to G to the zero
cocycle from F to K. -/
@[simp] theorem zero_postcomp (f : G ⟶ K) :
    (0 : Cocycle F G n).postcomp f = 0 := by
  apply Cocycle.ext
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C be a preadditive category and F,G,H,K,L be integer-indexed cochain complexes in C. Let a,m
∈ ℤ with m+a=0. Under the equivalence Hom(K[a],L) ≅ Zᵐ Hom(K,L), a map f : K[a] → L precomposed
with g[a] for g : K′ → K corresponds to the cocycle of f precomposed with g. -/
theorem equivHomShift'_shift_comp {K' : CochainComplex C ℤ} {a m : ℤ} (h : m + a = 0)
    (g : K' ⟶ K) (f : K⟦a⟧ ⟶ L) :
    equivHomShift' a m h (g⟦a⟧' ≫ f) = Cocycle.precomp (equivHomShift' a m h f) g := by
  ext p q hpq
  have hqa : q + a = p := by omega
  subst hqa
  simp only [equivHomShift'_apply, Cocycle.leftUnshift_coe,
    Cochain.leftUnshift_v _ _ _ _ _ _ _ (add_zero q), precomp_coe,
    Cochain.zero_cochain_comp_v, Cocycle.ofHom_coe, Cochain.ofHom_v]
  erw [Category.id_comp]
  rw [Linear.comp_units_smul, ← Category.assoc]
  congr 1
  dsimp only [shiftFunctorObjXIso]
  simp only [Category.assoc]
  erw [Category.id_comp]
  rw [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C be a preadditive category and F,G,H,K,L be integer-indexed cochain complexes in C. Let a,m
∈ ℤ with m+a=0. Under Hom(K[a],L) ≅ Zᵐ Hom(K,L), postcomposing f : K[a] → L with g : L → L′
corresponds to postcomposing its degree-m cocycle with g. -/
theorem equivHomShift'_comp {L' : CochainComplex C ℤ} {a m : ℤ} (h : m + a = 0)
    (f : K⟦a⟧ ⟶ L) (g : L ⟶ L') :
    equivHomShift' a m h (f ≫ g) = Cocycle.postcomp (equivHomShift' a m h f) g := by
  ext p q hpq
  simp [equivHomShift'_apply, Cochain.leftUnshift_v _ _ _ _ _ _ _ (add_zero q)]

end CochainComplex.HomComplex.Cocycle
