/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Basic

/-!
# Presentations of the Chevalley–Eilenberg bracket boundary

Let R be a commutative ring and L an R-Lie algebra. For an ordered (n+1)-tuple x,
the bracket prescription is the sum over i<j of (−1)^{i+j}[xᵢ,xⱼ] wedged with
the remaining entries in their original order. The bracket is placed first; in degree
two the prescription is −[x,y], and the degree-one boundary is zero.

Presented differential data agree with a prescribed tuple formula on decomposable wedges.
Such a presentation determines every differential uniquely. Lie homomorphisms preserve the
bracket prescription, so their exterior maps commute with the presented differentials.
Canonical constructs this presentation from the square-zero exterior-algebra boundary.
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
theorem compatible_of_boundary_natural
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

-- Retain the published name for existing presented-data callers.
abbrev homOfBoundaryNatural
    {L' : Type v} [LieRing L'] [LieAlgebra R L']
    {boundary : PureBoundary R L} {boundary' : PureBoundary R L'}
    (D : PresentedData R L boundary) (D' : PresentedData R L' boundary')
    (f : L →ₗ⁅R⁆ L') (hf : BoundaryNatural R L boundary boundary' f) :
    Hom (R := R) (L := L) D.toChainData D'.toChainData f :=
  compatible_of_boundary_natural R L D D' f hf

end ChainData
end ChevalleyEilenberg
