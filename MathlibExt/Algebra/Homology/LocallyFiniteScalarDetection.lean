/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Linear.ScalarDetection
public import MathlibExt.Algebra.Homology.LocallyFiniteIdempotentImages
public import MathlibExt.Algebra.Homology.Linear
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Data.Nat.Basic

/-!
# Scalar detection on locally finite idempotent-image homology

Let C be an abelian R-linear category for a semiring R. A complex K has orthogonal idempotents
e_j and degreewise bounds N(n) with (e_j)_n=0 for j>N(n) and Σ_{j≤N(n)}(e_j)_n=id. Their chain
images E_j have split homology inclusions I_j and projections P_j, with a finite identity sum in
each degree.

Suppose d:K→D,m:D→K satisfy e_j≫d≫m=a_j•e_j. On homology, H_n(d)≫H_n(m)≫P_j=a_j•P_j. A map
annihilated by H_n(d) has zero j-projection when a_j•id_{H_n(E_j)} is mono. If all other active
image scalars are monic, that map is fixed by H_n(e_j).

If e_j≫d=0 as a chain map, these conditions give H_n(E_j)≅ker(H_n(d)). This is homology of the
idempotent-image complex compared with the kernel of the homology map. For module categories
scalar injectivity on the image homologies supplies monicity. Over a rational algebra, the
weights 2^j-2 are units outside j=1, so the same chain-annihilation condition identifies the
weight-one image homology with that kernel.
-/

@[expose] public section

noncomputable section

universe t u v w

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace HomologicalComplex

variable {R : Type t} [Semiring R]
    {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
    {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (e : ℕ → (K ⟶ K))
    (he : ∀ i j : ℕ, e i ≫ e j = if i = j then e i else 0)
    (N : ι → ℕ)
    (hsupport : ∀ n j, N n < j → (e j).f n = 0)
    (hsum : ∀ n, (∑ j : Fin (N n + 1), (e j.val).f n) = 𝟙 (K.X n))

include hsum in
omit [Linear R C] in
/-- Let C be abelian in object/morphism universes u,v, c a complex shape on I in w, K a c-shaped
complex, and e_j:K→K a family indexed by j∈ℕ. Write E_j=image(e_j), i_j:E_j→K, and p_j:K→E_j for
its image factorization. Let N:I→ℕ and assume Σ_{j≤N(n)}(e_j)_n=id_{K_n} for every n. Then
Σ_{j≤N(n)}H_n(e_j)=id_{H_nK}. This sum identity uses the degree components and does not require
scalar linearity. -/
theorem idempotentHomology_sum (n : ι) :
    (∑ j : Fin (N n + 1), homologyMap (e j.val) n) = 𝟙 (K.homology n) := by
  classical
  let s : K ⟶ K := ∑ j : Fin (N n + 1), e j.val
  have hs : s.f n = 𝟙 (K.X n) :=
    ((eval C c n).map_sum (fun j : Fin (N n + 1) => e j.val) Finset.univ).trans
      (hsum n)
  change (∑ j : Fin (N n + 1), (homologyFunctor C c n).map (e j.val)) = _
  rw [← Functor.map_sum]
  exact homologyMap_eq_id_of_component n s hs

include he in
omit [Linear R C] in
/-- Let C be abelian in object/morphism universes u,v, c a complex shape on I in w, K a c-shaped
complex, and e_j:K→K a family indexed by j∈ℕ. Write E_j=image(e_j), i_j:E_j→K, and p_j:K→E_j for
its image factorization. Assume e_j≫e_k=e_j when j=k and zero otherwise. For every n,j,
H_n(i_j)≫H_n(p_j)=id_{H_n(E_j)}. The chain image of the idempotent is split by its factorization
map. -/
theorem imageHomology_split (n : ι) (j : ℕ) :
    homologyMap (image.ι (e j)) n ≫ homologyMap (factorThruImage (e j)) n =
      𝟙 ((image (e j)).homology n) := by
  rw [← homologyMap_comp, idempotentImage_split K e he j, homologyMap_id]

include he in
omit [Linear R C] in
/-- Let C be abelian in object/morphism universes u,v, c a complex shape on I in w, K a c-shaped
complex, and e_j:K→K a family indexed by j∈ℕ. Write E_j=image(e_j), i_j:E_j→K, and p_j:K→E_j for
its image factorization. Assume e_j≫e_k=e_j when j=k and zero otherwise. For n∈I and j≠k,
H_n(i_j)≫H_n(p_k)=0. Thus the inclusion from one chain-image homology followed by another image
projection vanishes. -/
theorem imageHomology_cross (n : ι) (j k : ℕ) (hjk : j ≠ k) :
    homologyMap (image.ι (e j)) n ≫ homologyMap (factorThruImage (e k)) n = 0 := by
  rw [← homologyMap_comp, idempotentImage_cross K e he j k hjk, homologyMap_zero]

include hsupport in
omit [Linear R C] in
/-- Let C be abelian in object/morphism universes u,v, c a complex shape on I in w, K a c-shaped
complex, and e_j:K→K a family indexed by j∈ℕ. Write E_j=image(e_j), i_j:E_j→K, and p_j:K→E_j for
its image factorization. Let N:I→ℕ and assume (e_j)_n=0 whenever j>N(n). For such j at n,
H_n(p_j):H_nK→H_n(E_j) is zero. -/
theorem imageHomology_support (n : ι) (j : ℕ) (hj : N n < j) :
    homologyMap (factorThruImage (e j)) n = 0 :=
  homologyMap_eq_zero_of_component n (factorThruImage (e j))
    (idempotentImage_factor_support K e N hsupport n j hj)

include hsum in
omit [Linear R C] in
/-- Let C be abelian in object/morphism universes u,v, c a complex shape on I in w, K a c-shaped
complex, and e_j:K→K a family indexed by j∈ℕ. Write E_j=image(e_j), i_j:E_j→K, and p_j:K→E_j for
its image factorization. If Σ_{j≤N(n)}(e_j)_n=id_{K_n} for every n, then
Σ_{j≤N(n)}H_n(p_j)≫H_n(i_j)=id_{H_nK}. Each product is H_n(e_j) by the image factorization. -/
theorem imageHomology_sum (n : ι) :
    (∑ j : Fin (N n + 1), homologyMap (factorThruImage (e j.val)) n ≫
      homologyMap (image.ι (e j.val)) n) = 𝟙 (K.homology n) := by
  simp_rw [← homologyMap_comp, image.fac]
  exact idempotentHomology_sum K e N hsum n

variable {D : HomologicalComplex C c}
    (d : K ⟶ D) (m : D ⟶ K) (a : ℕ → R)
    (hweight : ∀ j, e j ≫ d ≫ m = a j • e j)

include hweight in
private theorem idempotentImage_inclusion_weight (j : ℕ) :
    image.ι (e j) ≫ d ≫ m = a j • image.ι (e j) := by
  apply (cancel_epi (factorThruImage (e j))).mp
  simpa only [Category.assoc, image.fac_assoc, image.fac, Linear.comp_smul] using hweight j

include hweight in
/-- Let C be abelian in object/morphism universes u,v, c a complex shape on I in w, K a c-shaped
complex, and e_j:K→K a family indexed by j∈ℕ. Write E_j=image(e_j), i_j:E_j→K, and p_j:K→E_j for
its image factorization. Let R be a semiring in universe t and C be R-linear. Let d:K→D, m:D→K,
and a_j∈R satisfy e_j≫d≫m=a_j•e_j for every j. At degree n put A_j=H_n(E_j), I_j=H_n(i_j),
P_j=H_n(p_j), and δ=H_n(d), μ=H_n(m). For every n,j, I_j≫δ≫μ=a_j•I_j. This follows from the
chain weight equation and the image inclusion. -/
theorem imageHomology_weight (n : ι) (j : ℕ) :
    homologyMap (image.ι (e j)) n ≫ homologyMap d n ≫ homologyMap m n =
      a j • homologyMap (image.ι (e j)) n := by
  let H := homologyFunctor C c n
  change H.map (image.ι (e j)) ≫ H.map d ≫ H.map m = a j • H.map (image.ι (e j))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_smul]
  exact congrArg H.map (idempotentImage_inclusion_weight K e d m a hweight j)

include he hsupport hsum hweight in
/-- Let C be abelian in object/morphism universes u,v, c a complex shape on I in w, K a c-shaped
complex, and e_j:K→K a family indexed by j∈ℕ. Write E_j=image(e_j), i_j:E_j→K, and p_j:K→E_j for
its image factorization. Let R be a semiring in universe t and C be R-linear. Assume e_j≫e_k=e_j
when j=k and zero otherwise. Let N:I→ℕ satisfy (e_j)_n=0 for j>N(n) and
Σ_{j≤N(n)}(e_j)_n=id_{K_n} for every n. Let d:K→D, m:D→K, and a_j∈R satisfy e_j≫d≫m=a_j•e_j for
every j. At degree n put A_j=H_n(E_j), I_j=H_n(i_j), P_j=H_n(p_j), and δ=H_n(d), μ=H_n(m). For
every j, δ≫μ≫P_j=a_j•P_j as maps H_nK→A_j. The locally finite split decomposition converts the
inclusion-weight law into this post-projection equation. -/
theorem idempotentHomology_operator_projection (n : ι) (j : ℕ) :
    homologyMap d n ≫ homologyMap m n ≫ homologyMap (factorThruImage (e j)) n =
      a j • homologyMap (factorThruImage (e j)) n :=
  finiteSplit_operator_projection
    (fun k => (image (e k)).homology n)
    (fun k => homologyMap (image.ι (e k)) n)
    (fun k => homologyMap (factorThruImage (e k)) n)
    (imageHomology_split K e he n) (imageHomology_cross K e he n)
    (N n) (imageHomology_support K e N hsupport n) (imageHomology_sum K e N hsum n)
    (homologyMap d n) (homologyMap m n) a
    (fun j _ => imageHomology_weight K e d m a hweight n j) j

include he hsupport hsum hweight in
/-- Let C be abelian in object/morphism universes u,v, c a complex shape on I in w, K a c-shaped
complex, and e_j:K→K a family indexed by j∈ℕ. Write E_j=image(e_j), i_j:E_j→K, and p_j:K→E_j for
its image factorization. Let R be a semiring in universe t and C be R-linear. Assume e_j≫e_k=e_j
when j=k and zero otherwise. Let N:I→ℕ satisfy (e_j)_n=0 for j>N(n) and
Σ_{j≤N(n)}(e_j)_n=id_{K_n} for every n. Let d:K→D, m:D→K, and a_j∈R satisfy e_j≫d≫m=a_j•e_j for
every j. At degree n put A_j=H_n(E_j), I_j=H_n(i_j), P_j=H_n(p_j), and δ=H_n(d), μ=H_n(m). For
f:Z→H_nK with f≫δ=0 and any j, assume a_j•id_{A_j} is mono. Then f≫P_j=0. Monicity is required
on the image homology A_j. -/
theorem idempotentHomology_projection_zero_of_annihilated_map (n : ι) {Z : C}
    (f : Z ⟶ K.homology n) (hf : f ≫ homologyMap d n = 0) (j : ℕ)
    [Mono (a j • 𝟙 ((image (e j)).homology n))] :
    f ≫ homologyMap (factorThruImage (e j)) n = 0 :=
  finiteSplit_projection_zero_of_annihilated_map
    (fun k => (image (e k)).homology n)
    (fun k => homologyMap (image.ι (e k)) n)
    (fun k => homologyMap (factorThruImage (e k)) n)
    (imageHomology_split K e he n) (imageHomology_cross K e he n)
    (N n) (imageHomology_support K e N hsupport n) (imageHomology_sum K e N hsum n)
    (homologyMap d n) (homologyMap m n) a
    (fun j _ => imageHomology_weight K e d m a hweight n j)
    f hf j

include he hsupport hsum hweight in
/-- Let C be abelian in object/morphism universes u,v, c a complex shape on I in w, K a c-shaped
complex, and e_j:K→K a family indexed by j∈ℕ. Write E_j=image(e_j), i_j:E_j→K, and p_j:K→E_j for
its image factorization. Let R be a semiring in universe t and C be R-linear. Assume e_j≫e_k=e_j
when j=k and zero otherwise. Let N:I→ℕ satisfy (e_j)_n=0 for j>N(n) and
Σ_{j≤N(n)}(e_j)_n=id_{K_n} for every n. Let d:K→D, m:D→K, and a_j∈R satisfy e_j≫d≫m=a_j•e_j for
every j. At degree n put A_j=H_n(E_j), I_j=H_n(i_j), P_j=H_n(p_j), and δ=H_n(d), μ=H_n(m). For
f:Z→H_nK with f≫δ=0, fix j. If a_k•id_{A_k} is mono for every k≤N(n),k≠j, then f≫H_n(e_j)=f. The
distinguished index need not be within the active bound. -/
theorem idempotentHomology_projector_of_annihilated_map (n : ι) {Z : C}
    (f : Z ⟶ K.homology n) (hf : f ≫ homologyMap d n = 0) (j : ℕ)
    (hregular : ∀ k, k ≤ N n → k ≠ j → Mono (a k • 𝟙 ((image (e k)).homology n))) :
    f ≫ homologyMap (e j) n = f := by
  have h := finiteSplit_single_projector_of_annihilated_map
    (fun k => (image (e k)).homology n)
    (fun k => homologyMap (image.ι (e k)) n)
    (fun k => homologyMap (factorThruImage (e k)) n)
    (imageHomology_split K e he n) (imageHomology_cross K e he n)
    (N n) (imageHomology_support K e N hsupport n) (imageHomology_sum K e N hsum n)
    (homologyMap d n) (homologyMap m n) a
    (fun j _ => imageHomology_weight K e d m a hweight n j)
    f hf j hregular
  simpa only [← homologyMap_comp, image.fac] using h

include he hsupport hsum hweight in
/-- Let C be abelian in object/morphism universes u,v, c a complex shape on I in w, K a c-shaped
complex, and e_j:K→K a family indexed by j∈ℕ. Write E_j=image(e_j), i_j:E_j→K, and p_j:K→E_j for
its image factorization. Let R be a semiring in universe t and C be R-linear. Assume e_j≫e_k=e_j
when j=k and zero otherwise. Let N:I→ℕ satisfy (e_j)_n=0 for j>N(n) and
Σ_{j≤N(n)}(e_j)_n=id_{K_n} for every n. Let d:K→D, m:D→K, and a_j∈R satisfy e_j≫d≫m=a_j•e_j for
every j. At degree n put A_j=H_n(E_j), I_j=H_n(i_j), P_j=H_n(p_j), and δ=H_n(d), μ=H_n(m). Fix j
and assume a_k•id_{A_k} is mono for all k≤N(n),k≠j, and e_j≫d=0 as a chain map. Then A_j≅ker(δ).
Its forward map factors I_j through the kernel, and its inverse is kernel inclusion followed by
P_j. -/
def idempotentHomologyScalarKernelIso (n : ι) (j : ℕ)
    (hregular : ∀ k, k ≤ N n → k ≠ j → Mono (a k • 𝟙 ((image (e k)).homology n)))
    (hzero : e j ≫ d = 0) : (image (e j)).homology n ≅ kernel (homologyMap d n) := by
  have hi : image.ι (e j) ≫ d = 0 := by
    apply (cancel_epi (factorThruImage (e j))).mp
    simpa only [Category.assoc, image.fac_assoc, image.fac, comp_zero] using hzero
  have hiH : homologyMap (image.ι (e j)) n ≫ homologyMap d n = 0 := by
    rw [← homologyMap_comp, hi, homologyMap_zero]
  exact finiteSplitScalarKernelIso
    (fun k => (image (e k)).homology n)
    (fun k => homologyMap (image.ι (e k)) n)
    (fun k => homologyMap (factorThruImage (e k)) n)
    (imageHomology_split K e he n) (imageHomology_cross K e he n)
    (N n) (imageHomology_support K e N hsupport n) (imageHomology_sum K e N hsum n)
    (homologyMap d n) (homologyMap m n) a
    (fun j _ => imageHomology_weight K e d m a hweight n j)
    j hregular hiH

end HomologicalComplex

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- Let R be a commutative ring in u, M∈ModuleCat_v(R), and a∈R. If multiplication m↦a•m is
injective on M, then a•id_M is mono in the module category. The ring and carrier universes are
independent. -/
theorem mono_smul_id_of_isSMulRegular (M : ModuleCat.{v} R) (a : R)
    (ha : IsSMulRegular M a) : Mono (a • 𝟙 M) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  change Function.Injective (fun x : M => a • x)
  exact ha

end ModuleCat

namespace HomologicalComplex

variable {R : Type u} [CommRing R]
    {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (e : ℕ → (K ⟶ K))
    (he : ∀ i j : ℕ, e i ≫ e j = if i = j then e i else 0)
    (N : ι → ℕ)
    (hsupport : ∀ n j, N n < j → (e j).f n = 0)
    (hsum : ∀ n, (∑ j : Fin (N n + 1), (e j.val).f n) = 𝟙 (K.X n))
    {D : HomologicalComplex (ModuleCat.{v} R) c}
    (d : K ⟶ D) (m : D ⟶ K) (a : ℕ → R)
    (hweight : ∀ j, e j ≫ d ≫ m = a j • e j)

include he hsupport hsum hweight in
/-- Let R be a commutative ring in u, c a complex shape on I in w, and K,D complexes of R-modules
with carriers in v. Let e_j be orthogonal chain idempotents, with bounds N(n) satisfying
(e_j)_n=0 for j>N(n) and Σ_{j≤N(n)}(e_j)_n=id. Let d:K→D,m:D→K obey e_j≫d≫m=a_j•e_j. For
n∈I,j∈ℕ, assume e_j≫d=0 and each scalar a_k acts injectively on H_n(image(e_k)) for k≤N(n),k≠j.
Then H_n(image(e_j))≅ker(H_n(d)) as R-modules. The regularity hypotheses concern these image
homologies. -/
def moduleCatIdempotentHomologyScalarKernelIso (n : ι) (j : ℕ)
    (hregular : ∀ k, k ≤ N n → k ≠ j → IsSMulRegular ((image (e k)).homology n) (a k))
    (hzero : e j ≫ d = 0) : (image (e j)).homology n ≅ kernel (homologyMap d n) :=
  idempotentHomologyScalarKernelIso K e he N hsupport hsum d m a hweight n j
    (fun k hk hj => ModuleCat.mono_smul_id_of_isSMulRegular _ _ (hregular k hk hj)) hzero

end HomologicalComplex

/-- Let R be a ring in universe u with characteristic zero. For every natural j≠1, (2:R)^j-2≠0. This
includes j=0, when the scalar is -1. -/
theorem two_pow_sub_two_ne_zero (R : Type u) [Ring R] [CharZero R]
    (j : ℕ) (hj : j ≠ 1) : (2 : R) ^ j - 2 ≠ 0 := by
  intro h
  have hcast : (((2 : ℕ) ^ j : ℕ) : R) = ((2 : ℕ) : R) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (sub_eq_zero.mp h)
  have hnat : (2 : ℕ) ^ j = 2 := Nat.cast_injective hcast
  have hpow : (2 : ℕ) ^ j = (2 : ℕ) ^ 1 := by simpa only [pow_one] using hnat
  exact hj (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hpow)

/-- Let R be a commutative ℚ-algebra in universe u. For every j∈ℕ with j≠1, (2:R)^j-2 is a unit. It
is the image of the corresponding nonzero rational unit under the algebra map ℚ→R. -/
theorem two_pow_sub_two_isUnit (R : Type u) [CommRing R] [Algebra ℚ R]
    (j : ℕ) (hj : j ≠ 1) : IsUnit ((2 : R) ^ j - 2) := by
  have hq : IsUnit ((2 : ℚ) ^ j - 2) :=
    isUnit_iff_ne_zero.mpr (two_pow_sub_two_ne_zero ℚ j hj)
  have htwo : (algebraMap ℚ R) (2 : ℚ) = (2 : R) :=
    map_ofNat (algebraMap ℚ R) 2
  simpa only [map_sub, map_pow, htwo] using hq.map (algebraMap ℚ R)

namespace HomologicalComplex

variable {R : Type u} [CommRing R] [Algebra ℚ R]
    {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (e : ℕ → (K ⟶ K))
    (he : ∀ i j : ℕ, e i ≫ e j = if i = j then e i else 0)
    (N : ι → ℕ)
    (hsupport : ∀ n j, N n < j → (e j).f n = 0)
    (hsum : ∀ n, (∑ j : Fin (N n + 1), (e j.val).f n) = 𝟙 (K.X n))
    {D : HomologicalComplex (ModuleCat.{v} R) c}
    (d : K ⟶ D) (m : D ⟶ K)
    (hweight : ∀ j, e j ≫ d ≫ m = ((2 : R) ^ j - 2) • e j)

include he hsupport hsum hweight in
/-- Let R be a commutative ℚ-algebra in u and K,D c-shaped complexes of R-modules with carriers v,
for an index type I in w. Suppose e_j are orthogonal idempotents with degree bounds N(n), zero
components above the bounds and finite identity sums. If e_j≫d≫m=(2^j-2)•e_j for all j and
e₁≫d=0, then H_n(image(e₁))≅ker(H_n(d)) for every n∈I. All other active scalars are units on
their image homologies. -/
def moduleCatIdempotentHomologyDyadicKernelIso (n : ι) (hzero : e 1 ≫ d = 0) :
    (image (e 1)).homology n ≅ kernel (homologyMap d n) :=
  moduleCatIdempotentHomologyScalarKernelIso K e he N hsupport hsum d m
    (fun j => (2 : R) ^ j - 2) hweight n 1
    (fun j _ hj => (two_pow_sub_two_isUnit R j hj).isSMulRegular _) hzero

end HomologicalComplex
