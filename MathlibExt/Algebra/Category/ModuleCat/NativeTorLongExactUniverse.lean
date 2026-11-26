/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.TorBalancedNaturality
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ParameterMap
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tor connecting homomorphisms and exact windows in both variables

Let R be commutative in universe u and coefficient modules lie in W=max(u,v). Tensoring with any
fixed module is right exact, so Tor_0^R(M,N)≅M⊗_R N. For 0→A→B→C→0, the canonical connecting map
δ_q:Tor_{q+1}(M,C)→Tor_q(M,A) joins the five-arrow exact window
Tor_{q+1}(M,A)→Tor_{q+1}(M,B)→Tor_{q+1}(M,C)→Tor_q(M,A)→Tor_q(M,B)→Tor_q(M,C). Its degree-zero
final map is epic.

The connecting maps are natural both in maps of short exact sequences and in the fixed
coefficient M. If Tor_{q+1}(M,B)=0 and Tor_q(M,a)=0, then δ_q is an isomorphism. Canonical Tor
symmetry defines the corresponding first-variable connecting map and identifies its complete
window with the second-variable one, preserving all coefficient maps and the degree-zero
epimorphism. The lift height v is independent of u.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor

namespace ModuleCat.UniverseTensor

universe u v
variable (R : Type u) [CommRing R]

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. For any coefficient M, the functor N↦M⊗_R N preserves finite
colimits. It sends a short exact sequence to an exact right-end sequence and preserves its
epimorphic quotient map, by tensor right exactness. -/
theorem nativeTensorLeft_preservesFiniteColimits (M : ModuleCat.{max u v} R) :
    PreservesFiniteColimits ((tensoringLeft (ModuleCat.{max u v} R)).obj M) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).2
  intro S hS
  have hg : Function.Surjective S.g :=
    (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  constructor
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact lTensor_exact M
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) hg
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact LinearMap.lTensor_surjective M hg

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. For M,N in W, the canonical comparison is Tor_0^R(M,N)≅M⊗_R N. It is
the degree-zero left-derived comparison for the right-exact functor M⊗_R(-), so the target is
the tensor product of the given module carriers. -/
def nativeTorZeroIso (M N : ModuleCat.{max u v} R) :
    (((Tor (ModuleCat.{max u v} R) 0).obj M).obj N) ≅
      ModuleCat.of R (M ⊗[R] N) := by
  let F := (tensoringLeft (ModuleCat.{max u v} R)).obj M
  letI : PreservesFiniteColimits F := nativeTensorLeft_preservesFiniteColimits R M
  exact F.leftDerivedZeroIsoSelf.app N

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. For fixed M and a map f:N→N′, let e_N:Tor_0^R(M,N)≅M⊗_R N and e_{N′}
be the zero-degree comparisons. Then Tor_0^R(id_M,f)≫e_{N′}.hom=e_N.hom≫(id_M⊗f). The equation
compares the same resolved-coefficient map on Tor and tensor product. -/
@[reassoc]
theorem nativeTorZeroIso_hom_naturality_resolved (M : ModuleCat.{max u v} R)
    {N N' : ModuleCat.{max u v} R} (f : N ⟶ N') :
    ((Tor (ModuleCat.{max u v} R) 0).obj M).map f ≫
        (nativeTorZeroIso R M N').hom =
      (nativeTorZeroIso R M N).hom ≫ ModuleCat.ofHom (f.hom.lTensor M) := by
  let F := (tensoringLeft (ModuleCat.{max u v} R)).obj M
  let : PreservesFiniteColimits F := nativeTensorLeft_preservesFiniteColimits R M
  exact F.leftDerivedZeroIsoSelf.hom.naturality f

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. Let 0→A→B→C→0 be a short exact sequence, with arrows a:A→B and b:B→C.
For a coefficient M and q∈ℕ, this is δ_q:Tor_{q+1}^R(M,C)→Tor_q^R(M,A), the connecting
homomorphism of the left-derived tensor functor M⊗_R(-). It is obtained from the projective
horseshoe homology boundary. -/
def nativeTorConnecting (M : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    (((Tor (ModuleCat.{max u v} R) (q + 1)).obj M).obj S.X₃) ⟶
      (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₁) :=
  LeftDerivedDelta.LDdelta ((tensoringLeft (ModuleCat.{max u v} R)).obj M) q S hS

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. Let 0→A→B→C→0 be a short exact sequence, with arrows a:A→B and b:B→C.
For M and q∈ℕ, this diagram is Tor_{q+1}(M,A)→Tor_{q+1}(M,B)→Tor_{q+1}(M,C) --δ_q→
Tor_q(M,A)→Tor_q(M,B)→Tor_q(M,C). The four coefficient maps are induced by a,b, and the middle
arrow is the canonical connecting map. -/
def nativeTorLongExactWindow (M : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    ComposableArrows (ModuleCat.{max u v} R) 5 :=
  ComposableArrows.mk₅
    (((Tor (ModuleCat.{max u v} R) (q + 1)).obj M).map S.f)
    (((Tor (ModuleCat.{max u v} R) (q + 1)).obj M).map S.g)
    (nativeTorConnecting R M S hS q)
    (((Tor (ModuleCat.{max u v} R) q).obj M).map S.f)
    (((Tor (ModuleCat.{max u v} R) q).obj M).map S.g)

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. Let 0→A→B→C→0 be a short exact sequence, with arrows a:A→B and b:B→C.
For M and q∈ℕ, the window
Tor_{q+1}(M,A)→Tor_{q+1}(M,B)→Tor_{q+1}(M,C)→Tor_q(M,A)→Tor_q(M,B)→Tor_q(M,C) is exact at each
of its four interior objects. The middle arrow is the left-derived tensor boundary δ_q. -/
theorem nativeTorLongExactWindow_exact (M : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    (nativeTorLongExactWindow R M S hS q).Exact :=
  LeftDerivedDelta.LDlongSequence_exact
    ((tensoringLeft (ModuleCat.{max u v} R)).obj M) q S hS

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. Let 0→A→B→C→0 be a short exact sequence, with arrows a:A→B and b:B→C.
For any fixed M, the map Tor_0^R(M,b):Tor_0^R(M,B)→Tor_0^R(M,C) is epic. Through Tor_0≅tensor,
it is the epimorphism id_M⊗b furnished by tensor right exactness. -/
theorem nativeTor_epi_zero (M : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) :
    Epi (((Tor (ModuleCat.{max u v} R) 0).obj M).map S.g) :=
  LeftDerivedDelta.LDepi_zero ((tensoringLeft (ModuleCat.{max u v} R)).obj M) S hS

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. Let S=(0→A→B→C→0) and S′=(0→A′→B′→C′→0) be short exact and f:S→S′ a
morphism with endpoint maps f_A,f_C. For M and q∈ℕ,
Tor_{q+1}(M,f_C)≫δ_{S′,q}=δ_{S,q}≫Tor_q(M,f_A). The equation uses the specified connecting maps
of the two sequences. -/
@[reassoc]
theorem nativeTorConnecting_naturality_sequence (M : ModuleCat.{max u v} R)
    {S S' : ShortComplex (ModuleCat.{max u v} R)} (f : S ⟶ S')
    (hS : S.ShortExact) (hS' : S'.ShortExact) (q : ℕ) :
    ((Tor (ModuleCat.{max u v} R) (q + 1)).obj M).map f.τ₃ ≫
        nativeTorConnecting R M S' hS' q =
      nativeTorConnecting R M S hS q ≫
        ((Tor (ModuleCat.{max u v} R) q).obj M).map f.τ₁ :=
  LeftDerivedDelta.LDdelta_natural
    ((tensoringLeft (ModuleCat.{max u v} R)).obj M) q S' S f hS' hS

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. Let 0→A→B→C→0 be a short exact sequence, with arrows a:A→B and b:B→C.
For a coefficient map f:M→M′ and q∈ℕ, Tor_{q+1}(f,id_C)≫δ_{M′,q}=δ_{M,q}≫Tor_q(f,id_A). Thus the
boundary square retains the map in the variable not resolved by the short exact sequence. -/
@[reassoc]
theorem nativeTorConnecting_naturality_coefficient
    {M M' : ModuleCat.{max u v} R} (f : M ⟶ M')
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    ((Tor (ModuleCat.{max u v} R) (q + 1)).map f).app S.X₃ ≫
        nativeTorConnecting R M' S hS q =
      nativeTorConnecting R M S hS q ≫
        ((Tor (ModuleCat.{max u v} R) q).map f).app S.X₁ :=
  LeftDerivedDelta.LDdelta_natural_functor
    ((tensoringLeft (ModuleCat.{max u v} R)).map f) q S hS

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. Let 0→A→B→C→0 be a short exact sequence, with arrows a:A→B and b:B→C.
For M and q∈ℕ, assume Tor_{q+1}(M,B)=0 and the map Tor_q(id_M,a):Tor_q(M,A)→Tor_q(M,B) is zero.
Then δ_q:Tor_{q+1}(M,C)→Tor_q(M,A) is an isomorphism. Exactness makes it monic after the zero
incoming map and epic before the zero outgoing map. -/
theorem nativeTorConnecting_isIso (M : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ)
    (h₂ : IsZero (((Tor (ModuleCat.{max u v} R) (q + 1)).obj M).obj S.X₂))
    (hf : ((Tor (ModuleCat.{max u v} R) q).obj M).map S.f = 0) :
    IsIso (nativeTorConnecting R M S hS q) := by
  let F := (tensoringLeft (ModuleCat.{max u v} R)).obj M
  change IsIso (LeftDerivedDelta.LDdelta F q S hS)
  let δ := LeftDerivedDelta.LDdelta F q S hS
  have h₂' : IsZero ((F.leftDerived (q + 1)).obj S.X₂) := h₂
  have hf' : (F.leftDerived q).map S.f = 0 := hf
  obtain ⟨wC, hC⟩ := LeftDerivedDelta.LDexact_C F q S hS
  obtain ⟨wA, hA⟩ := LeftDerivedDelta.LDexact_A F q S hS
  let C : ShortComplex (ModuleCat.{max u v} R) :=
    ShortComplex.mk ((F.leftDerived (q + 1)).map S.g) δ wC
  let A : ShortComplex (ModuleCat.{max u v} R) :=
    ShortComplex.mk δ ((F.leftDerived q).map S.f) wA
  have hg : (F.leftDerived (q + 1)).map S.g = 0 := h₂'.eq_of_src _ _
  have : Mono C.g := (C.exact_iff_mono hg).mp hC
  have : Epi A.f := (A.exact_iff_epi hf').mp hA
  change IsIso δ
  exact isIso_of_mono_of_epi _

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. Let 0→A→B→C→0 be a short exact sequence, with arrows a:A→B and b:B→C.
For N and q∈ℕ, let σ_{M,N}:Tor_q(M,N)≅Tor_q(N,M) denote the canonical Tor symmetry in the
indicated degree. This first-variable boundary Tor_{q+1}(C,N)→Tor_q(A,N) is
σ_{N,C}^{-1}≫δ_{N,q}≫σ_{N,A}, with symmetry degrees q+1 at the source and q at the target. -/
def nativeTorConnectingFirst (N : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    (((Tor (ModuleCat.{max u v} R) (q + 1)).obj S.X₃).obj N) ⟶
      (((Tor (ModuleCat.{max u v} R) q).obj S.X₁).obj N) :=
  (nativeTorSymmetry R N S.X₃ (q + 1)).inv ≫ nativeTorConnecting R N S hS q ≫
    (nativeTorSymmetry R N S.X₁ q).hom

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. Let 0→A→B→C→0 be a short exact sequence, with arrows a:A→B and b:B→C.
For fixed N and q∈ℕ, this diagram is
Tor_{q+1}(A,N)→Tor_{q+1}(B,N)→Tor_{q+1}(C,N)→Tor_q(A,N)→Tor_q(B,N)→Tor_q(C,N). Its four maps
come from a,b in the first variable, and its middle map is the symmetry-transported connecting
homomorphism. -/
def nativeTorLongExactWindowFirst (N : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    ComposableArrows (ModuleCat.{max u v} R) 5 :=
  ComposableArrows.mk₅
    (((Tor (ModuleCat.{max u v} R) (q + 1)).map S.f).app N)
    (((Tor (ModuleCat.{max u v} R) (q + 1)).map S.g).app N)
    (nativeTorConnectingFirst R N S hS q)
    (((Tor (ModuleCat.{max u v} R) q).map S.f).app N)
    (((Tor (ModuleCat.{max u v} R) q).map S.g).app N)

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. Let 0→A→B→C→0 be a short exact sequence, with arrows a:A→B and b:B→C.
For N and q∈ℕ, the six canonical symmetry isomorphisms identify the first-variable window on
Tor_{q+1}(A,N), Tor_{q+1}(B,N), Tor_{q+1}(C,N), Tor_q(A,N), Tor_q(B,N), Tor_q(C,N) with the
second-variable window with N first. Naturality supplies the four coefficient squares, and the
definition of the first boundary supplies the connecting square. -/
private def nativeTorLongExactWindowFirstIso (N : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    nativeTorLongExactWindowFirst R N S hS q ≅ nativeTorLongExactWindow R N S hS q := by
  let E₁ := ((nativeTorSymmetryNatIso R (q + 1)).app N).symm
  let E₀ := ((nativeTorSymmetryNatIso R q).app N).symm
  refine ComposableArrows.isoMk₅
    (E₁.app S.X₁) (E₁.app S.X₂) (E₁.app S.X₃)
    (E₀.app S.X₁) (E₀.app S.X₂) (E₀.app S.X₃) ?_ ?_ ?_ ?_ ?_
  · exact E₁.hom.naturality S.f
  · exact E₁.hom.naturality S.g
  · change (E₁.app S.X₃).hom ≫ nativeTorConnecting R N S hS q ≫
        (E₀.app S.X₁).inv ≫ (E₀.app S.X₁).hom =
      (E₁.app S.X₃).hom ≫ nativeTorConnecting R N S hS q
    simp only [Iso.inv_hom_id, Category.comp_id]
  · exact E₀.hom.naturality S.f
  · exact E₀.hom.naturality S.g

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. Let 0→A→B→C→0 be a short exact sequence, with arrows a:A→B and b:B→C.
For N and q∈ℕ, the canonical first-variable window
Tor_{q+1}(A,N)→Tor_{q+1}(B,N)→Tor_{q+1}(C,N)→Tor_q(A,N)→Tor_q(B,N)→Tor_q(C,N) is exact at its
four interior objects. The result transports second-variable exactness through the complete
symmetry isomorphism. -/
theorem nativeTorLongExactWindowFirst_exact (N : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    (nativeTorLongExactWindowFirst R N S hS q).Exact :=
  ComposableArrows.exact_of_iso (nativeTorLongExactWindowFirstIso R N S hS q).symm
    (nativeTorLongExactWindow_exact R N S hS q)

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. Let 0→A→B→C→0 be a short exact sequence, with arrows a:A→B and b:B→C.
For a fixed coefficient N, Tor_0^R(b,id_N):Tor_0^R(B,N)→Tor_0^R(C,N) is an epimorphism. It is
the symmetry transport of the right-exact degree-zero quotient map in the second variable. -/
theorem nativeTor_epi_zero_first (N : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) :
    Epi (((Tor (ModuleCat.{max u v} R) 0).map S.g).app N) := by
  have : Epi (((Tor (ModuleCat.{max u v} R) 0).obj N).map S.g) :=
    nativeTor_epi_zero R N S hS
  let E := ((nativeTorSymmetryNatIso R 0).app N).symm
  let e : Arrow.mk (((Tor (ModuleCat.{max u v} R) 0).map S.g).app N) ≅
      Arrow.mk (((Tor (ModuleCat.{max u v} R) 0).obj N).map S.g) :=
    Arrow.isoMk (E.app S.X₂) (E.app S.X₃) (E.hom.naturality S.g).symm
  exact ((MorphismProperty.epimorphisms (ModuleCat.{max u v} R)).arrow_mk_iso_iff e).mpr
    (MorphismProperty.epimorphisms.infer_property _)

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. For a morphism f between short exact sequences S=(0→A→B→C→0) and
S′=(0→A′→B′→C′→0), fixed N and q∈ℕ, the transported boundaries satisfy
Tor_{q+1}(f_C,id_N)≫δ′_{S′,q}=δ′_{S,q}≫Tor_q(f_A,id_N). Both sequences and their specified
endpoint maps enter the square. -/
@[reassoc]
theorem nativeTorConnectingFirst_naturality_sequence (N : ModuleCat.{max u v} R)
    {S S' : ShortComplex (ModuleCat.{max u v} R)} (f : S ⟶ S')
    (hS : S.ShortExact) (hS' : S'.ShortExact) (q : ℕ) :
    ((Tor (ModuleCat.{max u v} R) (q + 1)).map f.τ₃).app N ≫
        nativeTorConnectingFirst R N S' hS' q =
      nativeTorConnectingFirst R N S hS q ≫
        ((Tor (ModuleCat.{max u v} R) q).map f.τ₁).app N := by
  let E₁ := ((nativeTorSymmetryNatIso R (q + 1)).app N).symm
  let E₀ := ((nativeTorSymmetryNatIso R q).app N).symm
  have hδ := (nativeTorConnecting_naturality_sequence R N f hS hS' q).symm
  have h := Iso.conjugate_naturality (E₁.app S'.X₃) (E₁.app S.X₃)
    (E₀.app S'.X₁) (E₀.app S.X₁)
    (nativeTorConnecting R N S' hS' q) (nativeTorConnecting R N S hS q)
    (((Tor (ModuleCat.{max u v} R) (q + 1)).map f.τ₃).app N)
    (((Tor (ModuleCat.{max u v} R) q).map f.τ₁).app N)
    (((Tor (ModuleCat.{max u v} R) (q + 1)).obj N).map f.τ₃)
    (((Tor (ModuleCat.{max u v} R) q).obj N).map f.τ₁)
    (E₁.hom.naturality f.τ₃) (E₀.inv.naturality f.τ₁) hδ
  exact h.symm

private theorem nativeTorSymmetry_parameter_hom
    {N N' : ModuleCat.{max u v} R} (g : N ⟶ N') (X : ModuleCat.{max u v} R) (q : ℕ) :
    ((Tor (ModuleCat.{max u v} R) q).map g).app X ≫ (nativeTorSymmetry R N' X q).hom =
      (nativeTorSymmetry R N X q).hom ≫ ((Tor (ModuleCat.{max u v} R) q).obj X).map g := by
  let T := Tor (ModuleCat.{max u v} R) q
  let E := nativeTorSymmetryNatIso R q
  exact congrArg (fun a : T.obj N ⟶ T.flip.obj N' => a.app X) (E.hom.naturality g)

private theorem nativeTorSymmetry_parameter_inv
    {N N' : ModuleCat.{max u v} R} (g : N ⟶ N') (X : ModuleCat.{max u v} R) (q : ℕ) :
    ((Tor (ModuleCat.{max u v} R) q).obj X).map g ≫ (nativeTorSymmetry R N' X q).inv =
      (nativeTorSymmetry R N X q).inv ≫ ((Tor (ModuleCat.{max u v} R) q).map g).app X := by
  let T := Tor (ModuleCat.{max u v} R) q
  let E := nativeTorSymmetryNatIso R q
  exact congrArg (fun a : T.flip.obj N ⟶ T.obj N' => a.app X) (E.inv.naturality g)

/-- Let R be a commutative ring in universe u, with coefficient modules in W=max(u,v) for an
independent lift height v. Let 0→A→B→C→0 be a short exact sequence, with arrows a:A→B and b:B→C.
For a map g:N→N′ and q∈ℕ, the first-variable boundaries satisfy
Tor_{q+1}(id_C,g)≫δ′_{N′,q}=δ′_{N,q}≫Tor_q(id_A,g). The equality follows from naturality of the
canonical symmetry and of the second-variable boundary. -/
@[reassoc]
theorem nativeTorConnectingFirst_naturality_coefficient
    {N N' : ModuleCat.{max u v} R} (g : N ⟶ N')
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ) :
    ((Tor (ModuleCat.{max u v} R) (q + 1)).obj S.X₃).map g ≫
        nativeTorConnectingFirst R N' S hS q =
      nativeTorConnectingFirst R N S hS q ≫
        ((Tor (ModuleCat.{max u v} R) q).obj S.X₁).map g := by
  let T₁ := Tor (ModuleCat.{max u v} R) (q + 1)
  let T₀ := Tor (ModuleCat.{max u v} R) q
  have hs := nativeTorSymmetry_parameter_inv R g S.X₃ (q + 1)
  have ht := nativeTorSymmetry_parameter_hom R g S.X₁ q
  have hδ := (nativeTorConnecting_naturality_coefficient R g S hS q).symm
  have h := Iso.conjugate_naturality
    (nativeTorSymmetry R N' S.X₃ (q + 1)).symm
    (nativeTorSymmetry R N S.X₃ (q + 1)).symm
    (nativeTorSymmetry R N' S.X₁ q).symm (nativeTorSymmetry R N S.X₁ q).symm
    (nativeTorConnecting R N' S hS q) (nativeTorConnecting R N S hS q)
    ((T₁.obj S.X₃).map g) ((T₀.obj S.X₁).map g)
    ((T₁.map g).app S.X₃) ((T₀.map g).app S.X₁) hs ht hδ
  exact h.symm

end ModuleCat.UniverseTensor
