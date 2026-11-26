/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.NativeTorEulerAdditivityUniverse
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import MathlibExt.CategoryTheory.Monoidal.Tor.Additive

/-!
# Projective bounds give Tor vanishing and finite Euler cutoffs

Let R be a commutative ring and modules lie in W=max(u,v), with the lift height independent of
the ring universe. A zero term P_q in a projective resolution P of N makes Tor_q(M,N)=0. If P
has zero terms from n onward, the vanishing holds for every q≥n. A projective-dimension bound
pd(N)≤d gives Tor_q(M,N)=0 for q>d, and canonical symmetry gives the corresponding results for
M. The strict bound pd(N)<0 means N is zero and includes vanishing in degree zero.

For a short exact sequence 0→A→B→C→0, a projective bound pd(M)≤d supplies the zero cutoff
Tor_{d+1}(M,C). If all three Tor families have finite lengths below d+1, their cutoff Euler sums
are additive. A bounded projective resolution of M supplies the analogous cutoff n. The same
projective bound on a fixed second coefficient gives first-variable Euler additivity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ModuleCat.UniverseTensor

namespace ModuleCat.UniverseTensor

universe u v
variable (R : Type u) [CommRing R]

/-- Let R be commutative in universe u and modules lie in W=max(u,v), with v independent. For M,N, a
projective resolution P of N and q∈ℕ, assume P_q is zero. Then Tor_q^R(M,N)=0, because the
degree-q term of M⊗_R P is zero and its homology computes Tor_q. The degree q may be zero. -/
theorem nativeTor_isZero_of_projectiveResolution_term (M N : ModuleCat.{max u v} R)
    (P : ProjectiveResolution N) (q : ℕ) (hP : IsZero (P.complex.X q)) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) := by
  let F := (tensoringLeft (ModuleCat.{max u v} R)).obj M
  have hX : IsZero (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).X q) :=
    F.map_isZero hP
  have hH := (HomologicalComplex.ExactAt.of_isZero hX).isZero_homology
  exact hH.of_iso (P.isoLeftDerivedObj F q)

/-- Let R be commutative in universe u and modules lie in W=max(u,v), with v independent. Let P be a
projective resolution of N and n∈ℕ such that P_q=0 for every q≥n. For any M and q≥n,
Tor_q^R(M,N)=0. The cutoff is the first excluded resolution degree, and the vanishing is
asserted in every degree at and above it. -/
theorem nativeTor_isZero_of_projectiveResolution_bound (M N : ModuleCat.{max u v} R)
    (P : ProjectiveResolution N) (n : ℕ)
    (hP : ∀ q, n ≤ q → IsZero (P.complex.X q)) (q : ℕ) (hq : n ≤ q) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) :=
  nativeTor_isZero_of_projectiveResolution_term R M N P q (hP q hq)

/-- Let R be commutative in universe u and modules lie in W=max(u,v), with v independent. Let P be a
projective resolution of M with P_q=0 for all q≥n. For every second coefficient N and every q≥n,
Tor_q^R(M,N)=0. Canonical Tor symmetry transports the resolution computation for M in the
resolved variable. -/
theorem nativeTor_isZero_of_projectiveResolution_bound_coefficient
    (M N : ModuleCat.{max u v} R) (P : ProjectiveResolution M) (n : ℕ)
    (hP : ∀ q, n ≤ q → IsZero (P.complex.X q)) (q : ℕ) (hq : n ≤ q) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) :=
  (nativeTor_isZero_of_projectiveResolution_bound R N M P n hP q hq).of_iso
    (nativeTorSymmetry R M N q)

/-- Let R be commutative in universe u and modules lie in W=max(u,v), with v independent. For M,N,
d,q∈ℕ, assume pd(N)≤d and d<q. Then Tor_q^R(M,N)=0. Successive projective covers and the long
exact Tor sequence reduce the assertion to a projective resolved coefficient. -/
theorem nativeTor_isZero_of_projectiveDimensionLE_resolved (M N : ModuleCat.{max u v} R)
    (d : ℕ) [HasProjectiveDimensionLE N d] (q : ℕ) (hq : d < q) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) := by
  induction d generalizing N q with
  | zero =>
    have : Projective N := (projective_iff_hasProjectiveDimensionLE_zero N).mpr inferInstance
    cases q with
    | zero => omega
    | succ q => exact isZero_Tor_succ_of_projective (ModuleCat.{max u v} R) M N q
  | succ d ih =>
    cases q with
    | zero => omega
    | succ q =>
      let S := N.projectiveShortComplex
      have hS : S.ShortExact := N.shortExact_projectiveShortComplex
      have hP : Projective S.X₂ := by
        dsimp [S]
        infer_instance
      have hN : HasProjectiveDimensionLT S.X₃ (d + 2) := by
        change HasProjectiveDimensionLT N (d + 2)
        infer_instance
      have : HasProjectiveDimensionLE S.X₁ d :=
        (hS.hasProjectiveDimensionLT_X₃_iff d hP).mp hN
      have hK := ih S.X₁ q (by omega)
      let F := (tensoringLeft (ModuleCat.{max u v} R)).obj M
      obtain ⟨_, hExact⟩ := LeftDerivedDelta.LDexact_C F q S hS
      let : Projective S.X₂ := hP
      exact hExact.isZero_of_both_isZero
        (isZero_Tor_succ_of_projective (ModuleCat.{max u v} R) M S.X₂ q) hK

/-- Let R be commutative in universe u and modules lie in W=max(u,v), with v independent. For M,N
and d,q∈ℕ, assume pd(M)≤d and q>d. Then Tor_q^R(M,N)=0, by symmetry with the
projective-dimension vanishing result in the resolved coefficient. -/
theorem nativeTor_isZero_of_projectiveDimensionLE_coefficient (M N : ModuleCat.{max u v} R)
    (d : ℕ) [HasProjectiveDimensionLE M d] (q : ℕ) (hq : d < q) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) :=
  (nativeTor_isZero_of_projectiveDimensionLE_resolved R N M d q hq).of_iso
    (nativeTorSymmetry R M N q)

/-- Let R be commutative in universe u and modules lie in W=max(u,v), with v independent. For M,N
and n,q∈ℕ, assume pd(N)<n and q≥n. Then Tor_q^R(M,N)=0. When n=0, the strict-bound convention
says N is the zero object, so every Tor degree vanishes; when n=d+1 it is the bound pd(N)≤d. -/
theorem nativeTor_isZero_of_projectiveDimensionLT_resolved (M N : ModuleCat.{max u v} R)
    (n : ℕ) [HasProjectiveDimensionLT N n] (q : ℕ) (hq : n ≤ q) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) := by
  cases n with
  | zero =>
    exact ((Tor (ModuleCat.{max u v} R) q).obj M).map_isZero
      (isZero_of_hasProjectiveDimensionLT_zero N)
  | succ d =>
    exact nativeTor_isZero_of_projectiveDimensionLE_resolved R M N d q (by omega)

/-- Let R be commutative in universe u and modules lie in W=max(u,v), with v independent. For M,N
and n,q∈ℕ, assume pd(M)<n and q≥n. Then Tor_q^R(M,N)=0. At n=0 the first coefficient is zero; at
positive n the result follows by canonical symmetry from resolved-coefficient vanishing. -/
theorem nativeTor_isZero_of_projectiveDimensionLT_coefficient (M N : ModuleCat.{max u v} R)
    (n : ℕ) [HasProjectiveDimensionLT M n] (q : ℕ) (hq : n ≤ q) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) :=
  (nativeTor_isZero_of_projectiveDimensionLT_resolved R N M n q hq).of_iso
    (nativeTorSymmetry R M N q)

/-- Let R be commutative in universe u and modules lie in W=max(u,v), with v independent. Let
pd(M)≤d and 0→A→B→C→0 be short exact. Assume Tor_q(M,A), Tor_q(M,B) and Tor_q(M,C) have finite
length for every q<d+1. Then χ_{d+1}(M,B)=χ_{d+1}(M,A)+χ_{d+1}(M,C), where χ_n sums (-1)^q times
the naturalized Tor lengths for q<n. The projective bound makes Tor_{d+1}(M,C)=0. -/
theorem rawNativeTorEulerSum_shortExactSecond_of_projectiveDimension
    (M : ModuleCat.{max u v} R) (d : ℕ) [HasProjectiveDimensionLE M d]
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact)
    (h₁ : ∀ q < d + 1,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₁) ≠ ⊤)
    (h₂ : ∀ q < d + 1,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₂) ≠ ⊤)
    (h₃ : ∀ q < d + 1,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₃) ≠ ⊤) :
    rawNativeTorEulerSum R M S.X₂ (d + 1) =
      rawNativeTorEulerSum R M S.X₁ (d + 1) + rawNativeTorEulerSum R M S.X₃ (d + 1) :=
  rawNativeTorEulerSum_shortExactSecond R M S hS (d + 1) h₁ h₂ h₃
    (nativeTor_isZero_of_projectiveDimensionLE_coefficient R M S.X₃ d (d + 1) (by omega))

/-- Let R be commutative in universe u and modules lie in W=max(u,v), with v independent. Let P
resolve M with P_q=0 for q≥n, and let 0→A→B→C→0 be short exact. If the three families
Tor_q(M,A), Tor_q(M,B), Tor_q(M,C) have finite length for q<n, then χ_n(M,B)=χ_n(M,A)+χ_n(M,C).
The resolution bound gives the required zero cutoff term Tor_n(M,C). -/
theorem rawNativeTorEulerSum_shortExactSecond_of_projectiveResolution
    (M : ModuleCat.{max u v} R) (P : ProjectiveResolution M) (n : ℕ)
    (hP : ∀ q, n ≤ q → IsZero (P.complex.X q))
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact)
    (h₁ : ∀ q < n,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₁) ≠ ⊤)
    (h₂ : ∀ q < n,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₂) ≠ ⊤)
    (h₃ : ∀ q < n,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₃) ≠ ⊤) :
    rawNativeTorEulerSum R M S.X₂ n =
      rawNativeTorEulerSum R M S.X₁ n + rawNativeTorEulerSum R M S.X₃ n :=
  rawNativeTorEulerSum_shortExactSecond R M S hS n h₁ h₂ h₃
    (nativeTor_isZero_of_projectiveResolution_bound_coefficient R M S.X₃ P n hP n le_rfl)

/-- Let R be commutative in universe u and modules lie in W=max(u,v), with v independent. Let
pd(N)≤d and 0→A→B→C→0 be short exact. Suppose Tor_q(A,N), Tor_q(B,N), Tor_q(C,N) have finite
length for q<d+1. Then χ_{d+1}(B,N)=χ_{d+1}(A,N)+χ_{d+1}(C,N), with the zero cutoff
Tor_{d+1}(C,N) supplied by the projective bound on N. -/
theorem rawNativeTorEulerSum_shortExactFirst_of_projectiveDimension
    (N : ModuleCat.{max u v} R) (d : ℕ) [HasProjectiveDimensionLE N d]
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact)
    (h₁ : ∀ q < d + 1,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj S.X₁).obj N) ≠ ⊤)
    (h₂ : ∀ q < d + 1,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj S.X₂).obj N) ≠ ⊤)
    (h₃ : ∀ q < d + 1,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj S.X₃).obj N) ≠ ⊤) :
    rawNativeTorEulerSum R S.X₂ N (d + 1) =
      rawNativeTorEulerSum R S.X₁ N (d + 1) + rawNativeTorEulerSum R S.X₃ N (d + 1) :=
  rawNativeTorEulerSum_shortExactFirst R N S hS (d + 1) h₁ h₂ h₃
    (nativeTor_isZero_of_projectiveDimensionLE_resolved R S.X₃ N d (d + 1) (by omega))

end ModuleCat.UniverseTensor
