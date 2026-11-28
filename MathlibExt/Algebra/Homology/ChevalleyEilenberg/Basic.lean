/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Exterior chain complexes and Lie-map compatibility

For a commutative ring R and an R-Lie algebra L, the degree-n exterior chain object is
Λ_R^n L. A square-zero family of R-linear maps Λ_R^{n+1}L → Λ_R^nL determines a
nonnegative chain complex in ModuleCat at max{u,v}, with independent scalar and Lie
carrier universes. Specified exterior coordinates transport the differential of a complex
to such a family.

A Lie homomorphism gives maps on these exterior powers. Compatibility with two differential
families means that their differential squares commute, and supplies the corresponding
chain map. Compatibility is stable under identity and composition.

The bracket prescription and its presentation are developed in Presentation, and its
canonical realization and coefficient complex are constructed by the corresponding
Chevalley–Eilenberg boundary owners.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
The degree-n trivial-coefficient chain object is the R-module
Λ_R^n L in ModuleCat at universe max{u,v}. -/
abbrev chainObject (n : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R (⋀[R]^n L)

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
For a Lie homomorphism f:L→L′ in the same carrier universe,
the degree-n chain-object map is Λ_R^n f. It sends
x_0∧⋯∧x_{n-1} to f(x_0)∧⋯∧f(x_{n-1}). -/
def chainObjectMap
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ L') (n : ℕ) : chainObject R L n ⟶ chainObject R L' n :=
  ModuleCat.ofHom (exteriorPower.map n f.toLinearMap)

@[simp]
theorem chainObjectMap_id (n : ℕ) :
    chainObjectMap R L (LieHom.id : L →ₗ⁅R⁆ L) n = 𝟙 _ := by
  change ModuleCat.ofHom (exteriorPower.map n LinearMap.id) = _
  rw [exteriorPower.map_id]
  rfl

@[simp]
theorem chainObjectMap_comp
    {L' L'' : Type v}
    [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
    (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'') (n : ℕ) :
    chainObjectMap R L f n ≫ chainObjectMap R L' g n =
      chainObjectMap R L (g.comp f) n := by
  rw [chainObjectMap, chainObjectMap, chainObjectMap]
  rw [← ModuleCat.ofHom_comp, ← exteriorPower.map_comp]
  rfl

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
ChainData consists of R-linear maps d_n:Λ_R^{n+1}L→Λ_R^nL
whose consecutive composites d_n d_{n+1} vanish. It specifies a
nonnegative chain complex on the exterior-power objects. -/
structure ChainData where
  /-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
For exterior chain data D, its degree-n differential is the
R-linear map D.d_n:Λ_R^{n+1}L→Λ_R^nL. -/
  d : ∀ n : ℕ, (⋀[R]^(n + 1) L) →ₗ[R] (⋀[R]^n L)
  /-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
The square-zero condition on exterior chain data is
D.d_n D.d_{n+1}=0:Λ_R^{n+2}L→Λ_R^nL for every n≥0. -/
  d_comp_d : ∀ n : ℕ, (d n).comp (d (n + 1)) = 0

namespace ChainData

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
Square-zero exterior data D determine the nonnegative R-module
chain complex with degree-n object Λ_R^nL and boundary
from n+1 to n equal to D.d_n. -/
def complex (D : ChainData R L) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of
    (chainObject R L)
    (fun n => ModuleCat.ofHom (D.d n))
    (fun n => by
      rw [← ModuleCat.ofHom_comp, D.d_comp_d, ModuleCat.ofHom_zero])

@[simp]
theorem complex_X (D : ChainData R L) (n : ℕ) :
    D.complex.X n = chainObject R L n :=
  rfl

@[simp]
theorem complex_d_succ (D : ChainData R L) (n : ℕ) :
    D.complex.d (n + 1) n = ModuleCat.ofHom (D.d n) := by
  simp [complex, ChainComplex.of_d]

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
Let K be a nonnegative R-module complex and e_n:K_n≅Λ_R^nL
specified degree isomorphisms. Transporting its boundary gives
D.d_n=e_n d^K_{n+1,n} e_{n+1}⁻¹ on the exterior objects,
with square zero. -/
def ofComplex
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (e : ∀ n : ℕ, K.X n ≅ chainObject R L n) : ChainData R L where
  d n := (e n).hom.hom.comp
    ((K.d (n + 1) n).hom.comp (e (n + 1)).inv.hom)
  d_comp_d n := by
    have h :
        ((e (n + 1 + 1)).inv ≫ K.d (n + 1 + 1) (n + 1) ≫
            (e (n + 1)).hom) ≫
          ((e (n + 1)).inv ≫ K.d (n + 1) n ≫ (e n).hom) = 0 := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      simp
    exact congrArg ModuleCat.Hom.hom h

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
Let L′ be another R-Lie algebra in the same carrier universe,
D,D′ exterior differential data and f:L→L′ a Lie homomorphism.
The proposition Hom D D′ f asserts D′.d_n Λ^{n+1}f=Λ^n f D.d_n for every n. -/
structure Hom
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    (D : ChainData R L) (D' : ChainData R L')
    (f : L →ₗ⁅R⁆ L') : Prop where
  /-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
For compatible data D,D′ and a Lie homomorphism f:L→L′,
the differential square is D′.d_n Λ^{n+1}f=Λ^n f D.d_n
in every exterior degree. -/
  comm : ∀ n : ℕ,
    (D'.d n).comp (exteriorPower.map (n + 1) f.toLinearMap) =
      (exteriorPower.map n f.toLinearMap).comp (D.d n)

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
For a Lie homomorphism f:L→L′ compatible with exterior
differential data D,D′, the maps Λ_R^n f form a chain map
D.complex→D′.complex. -/
def map
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    {D : ChainData R L} {D' : ChainData R L'}
    (f : L →ₗ⁅R⁆ L') (hf : Hom (R := R) (L := L) D D' f) :
    D.complex ⟶ D'.complex :=
  ChainComplex.ofHom
    (chainObjectMap R L f)
    (fun n => by
      rw [complex_d_succ, complex_d_succ]
      simp only [chainObjectMap]
      rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
      exact ModuleCat.hom_ext (hf.comm n))

@[simp]
theorem map_f
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    {D : ChainData R L} {D' : ChainData R L'}
    (f : L →ₗ⁅R⁆ L') (hf : Hom (R := R) (L := L) D D' f) (n : ℕ) :
    (map (R := R) (L := L) f hf).f n = chainObjectMap R L f n :=
  rfl

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
The identity Lie homomorphism is compatible with every exterior
differential datum D; each exterior identity commutes with D.d_n. -/
theorem Hom.id (D : ChainData R L) :
    Hom (R := R) (L := L) D D (LieHom.id : L →ₗ⁅R⁆ L) where
  comm n := by
    change (D.d n).comp (exteriorPower.map (n + 1) LinearMap.id) =
      (exteriorPower.map n LinearMap.id).comp (D.d n)
    rw [exteriorPower.map_id, exteriorPower.map_id]
    simp

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
Let compatible Lie maps f:(L,D)→(L′,D′) and
 g:(L′,D′)→(L″,D″) be given. Their composite g∘f is compatible
with D,D″, since the exterior differential squares compose. -/
theorem Hom.comp
    {L' L'' : Type v}
    [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
    {D : ChainData R L} {D' : ChainData R L'} {D'' : ChainData R L''}
    {f : L →ₗ⁅R⁆ L'} {g : L' →ₗ⁅R⁆ L''}
    (F : Hom (R := R) (L := L) D D' f)
    (G : Hom (R := R) (L := L') D' D'' g) :
    Hom (R := R) (L := L) D D'' (g.comp f) where
  comm n := by
    rw [LieHom.toLinearMap_comp, exteriorPower.map_comp,
      exteriorPower.map_comp]
    simp only [← LinearMap.comp_assoc]
    rw [G.comm n]
    simp only [LinearMap.comp_assoc]
    rw [F.comm n]

@[simp]
theorem map_id (D : ChainData R L) :
    map (R := R) (L := L) (LieHom.id : L →ₗ⁅R⁆ L)
        (Hom.id (R := R) (L := L) D) =
      𝟙 D.complex := by
  apply HomologicalComplex.hom_ext
  intro n
  change chainObjectMap R L (LieHom.id : L →ₗ⁅R⁆ L) n =
    𝟙 (chainObject R L n)
  exact chainObjectMap_id R L n

@[simp]
theorem map_comp
    {L' L'' : Type v}
    [LieRing L'] [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']
    {D : ChainData R L} {D' : ChainData R L'} {D'' : ChainData R L''}
    {f : L →ₗ⁅R⁆ L'} {g : L' →ₗ⁅R⁆ L''}
    (F : Hom (R := R) (L := L) D D' f)
    (G : Hom (R := R) (L := L') D' D'' g) :
    map (R := R) (L := L) f F ≫ map (R := R) (L := L') g G =
      map (R := R) (L := L) (g.comp f)
        (F.comp (R := R) (L := L) G) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, map_f, map_f, map_f,
    chainObjectMap_comp]

end ChainData

end ChevalleyEilenberg
