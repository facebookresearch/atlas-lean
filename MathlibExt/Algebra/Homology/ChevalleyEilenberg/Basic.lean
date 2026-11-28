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
# Exterior chain data and the Chevalley–Eilenberg bracket formula

Let R be a commutative ring and L a Lie algebra over R. The degree-n
trivial-coefficient chain object is Λ_R^n L. Differential data consist
of R-linear maps d_n : Λ_R^{n+1} L → Λ_R^n L with d_n d_{n+1}=0.
Their chain category is ModuleCat over R at max{u,v} for independent
scalar and Lie-algebra carrier universes.

A boundary prescription β_n assigns a value to each ordered (n+1)-tuple
in L. Presented differential data satisfy
d_n(x_0 ∧ ⋯ ∧ x_n)=β_n(x).
The canonical bracket prescription is zero for n=0 and, for n≥1,
β_n(x)=∑_{0≤i<j≤n} (−1)^{i+j}
[x_i,x_j] ∧ (the remaining entries in their given order).
Each bracket is put first; the boundary from degree two to one is
−[x,y].

Exterior-power maps of a Lie homomorphism give a chain map whenever
they commute with the supplied differentials. Naturality of the
boundary prescriptions proves this compatibility for presented data.
A complex with specified exterior-power coordinates can also be
transported to these differential objects.

Reference: C. Chevalley and S. Eilenberg, Cohomology theory of Lie groups
and Lie algebras, Transactions of the AMS 63 (1948).
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

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
A pure-boundary prescription is a family of functions
β_n:L^{n+1}→Λ_R^nL on ordered tuples, one for each n≥0.
PresentedData relates such a prescription to linear exterior differentials. -/
abbrev PureBoundary := ∀ n : ℕ, (Fin (n + 1) → L) → (⋀[R]^n L)

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
The canonical bracket prescription is β_0(x)=0 and, for n≥1,
β_n(x)=∑_{0≤i<j≤n}(−1)^{i+j}[x_i,x_j]∧x with entries i,j deleted.
The bracket is first and the remaining entries retain their order;
in exterior degree two this is −[x,y]. -/
noncomputable def bracketBoundary : PureBoundary R L
  | 0, _ => 0
  | n + 1, v =>
      ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i,
        ((-1 : R) ^ (i.val + j.val + 1)) •
          exteriorPower.ιMulti R (n + 1)
            (Matrix.vecCons ⁅v i.castSucc, v j.succ⁆
              (j.removeNth (i.castSucc.removeNth v)))

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
For a prescription β, PresentedData is square-zero exterior
chain data D satisfying D.d_n(x_0∧⋯∧x_n)=β_n(x)
on every decomposable wedge. -/
structure PresentedData (boundary : PureBoundary R L) extends ChainData R L where
  /-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
Presented exterior data D with prescription β satisfy
D.d_n(x_0∧⋯∧x_n)=β_n(x) for every ordered (n+1)-tuple x. -/
  d_apply_ιMulti : ∀ (n : ℕ) (v : Fin (n + 1) → L),
    d n (exteriorPower.ιMulti R (n + 1) v) = boundary n v

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
If D and E are two exterior differential data presented by the
same tuple prescription β, then D.d_n=E.d_n as R-linear maps
in every degree n. -/
theorem PresentedData.d_eq
    {boundary : PureBoundary R L}
    (D E : PresentedData R L boundary) (n : ℕ) : D.d n = E.d n := by
  apply exteriorPower.linearMap_ext
    (R := R) (n := n + 1) (M := L) (N := ⋀[R]^n L)
  apply AlternatingMap.ext
  intro v
  change D.d n (exteriorPower.ιMulti R (n + 1) v) =
    E.d n (exteriorPower.ιMulti R (n + 1) v)
  rw [D.d_apply_ιMulti, E.d_apply_ιMulti]

variable {R L} in
/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
For data presented by the canonical bracket prescription,
the differential Λ_R^1L→Λ_R^0L is zero. -/
theorem PresentedData.d_zero
    (D : PresentedData R L (bracketBoundary R L)) : D.d 0 = 0 := by
  apply exteriorPower.linearMap_ext
    (R := R) (n := 1) (M := L) (N := ⋀[R]^0 L)
  apply AlternatingMap.ext
  intro a
  change D.d 0 (exteriorPower.ιMulti R 1 a) = 0
  exact D.d_apply_ιMulti 0 a

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
Compatibility means D′.d_n Λ^{n+1}f=Λ^n f D.d_n for all n. -/
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
For prescriptions β on L and β′ on L′, and a Lie homomorphism
f:L→L′, boundary naturality means
β′_n(f∘x)=Λ_R^n f(β_n(x)) for every ordered (n+1)-tuple x. -/
def BoundaryNatural
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    (boundary : PureBoundary R L) (boundary' : PureBoundary R L')
    (f : L →ₗ⁅R⁆ L') : Prop :=
  ∀ (n : ℕ) (v : Fin (n + 1) → L),
    exteriorPower.map n f.toLinearMap (boundary n v) =
      boundary' n (fun i => f (v i))

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
Every Lie homomorphism f:L→L′ preserves the canonical bracket
prescriptions: β^{L′}_n(f∘x)=Λ_R^n f(β^L_n(x)).
The bracket-front placement and signs are the same on both sides. -/
theorem bracketBoundary_natural
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ L') :
    BoundaryNatural R L (bracketBoundary R L) (bracketBoundary R L') f := by
  intro n x
  cases n with
  | zero => simp [bracketBoundary]
  | succ n =>
      simp only [bracketBoundary, map_sum, map_smul,
        exteriorPower.map_apply_ιMulti, Function.comp_def]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hv :
          (fun k => f (Matrix.vecCons ⁅x i.castSucc, x j.succ⁆
            (j.removeNth (i.castSucc.removeNth x)) k)) =
            Matrix.vecCons ⁅f (x i.castSucc), f (x j.succ)⁆
              (j.removeNth (i.castSucc.removeNth fun i => f (x i))) := by
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · exact f.map_lie _ _
        · rfl
      congr 2

/-- Let R be a commutative ring and L a Lie algebra over R,
with its Lie ring structure.
Let D,D′ be presented by β,β′ and let f:L→L′ be a Lie
homomorphism with β′_n(f∘x)=Λ^n f(β_n(x)). Then the exterior
maps commute with the differentials of D,D′ in every degree. -/
theorem homOfBoundaryNatural
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    {boundary : PureBoundary R L} {boundary' : PureBoundary R L'}
    (D : PresentedData R L boundary) (D' : PresentedData R L' boundary')
    (f : L →ₗ⁅R⁆ L') (hf : BoundaryNatural R L boundary boundary' f) :
    Hom (R := R) (L := L) D.toChainData D'.toChainData f where
  comm n := by
    apply exteriorPower.linearMap_ext
      (R := R) (n := n + 1) (M := L) (N := ⋀[R]^n L')
    apply AlternatingMap.ext
    intro v
    change D'.d n
        (exteriorPower.map (n + 1) f.toLinearMap
          (exteriorPower.ιMulti R (n + 1) v)) =
      exteriorPower.map n f.toLinearMap
        (D.d n (exteriorPower.ιMulti R (n + 1) v))
    rw [exteriorPower.map_apply_ιMulti, D'.d_apply_ιMulti,
      D.d_apply_ιMulti, hf n v]
    rfl

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
