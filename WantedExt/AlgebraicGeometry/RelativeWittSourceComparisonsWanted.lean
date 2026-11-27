/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RelativeWittUnramifiedNormalization
public import MathlibExt.AlgebraicGeometry.RelativeWittGroupIndModels

/-!
# Direct Witt normalization and general reductive ind-geometry requests

Source: Zhu, arXiv:1407.8519v3, formula (0.1.2), pp. 2--3,
Theorem 1.4, p. 9, Proposition 1.20, p. 16, and Section 1.4.
All perfect residue-field and coefficient hypotheses are explicit.

The direct `W(R)` lattice transport uses the actual proved tensor and
localized ring equivalences. The general reductive target is the
original fpqc positive-loop quotient. Finite convolution maps retain
the actual twisted quotient, native multiplication, proper scheme fibres
and every transition/colimit square. Generic etale quotient descent and
the original Witt/loop maps are completed public inputs.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeWittSourceComparisons

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.RelativeWittCoefficientDVRModels
open MathlibExt.AlgebraicGeometry.RelativeWittLatticeModels
open MathlibExt.AlgebraicGeometry.RelativeWittUnramifiedNormalization
open MathlibExt.AlgebraicGeometry.RelativeWittGroupIndModels
open MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels

/-- Transport of lattices to Witt vectors: let $p$ be a prime, $k$ a perfect field of characteristic
$p$ (its Frobenius $x ↦ x^p$ is bijective), $n ∈ ℕ$, and `D` a scalar extension, along maps of
perfect $k$-algebras, of the lattices in $(W(R) ⊗_{W(k)} W(k))[1/p]^n$. Then for every perfect
$k$-algebra $R$ there is a bijection from these lattices to the finite projective $W(R)$-lattices in
$W(R)[1/p]^n$, given on coordinates by the ring isomorphism $(W(R) ⊗_{W(k)} W(k))[1/p] ≅ W(R)[1/p]$,
that carries the scalar extension `D` along $R → S$ to the $W(S)$-span of the image under
$W(R)[1/p] → W(S)[1/p]$ and preserves each bound $N$ (`LatticeComparison`). -/
public def_wanted unramifiedLatticeTransport
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (perfect : Function.Bijective (fun x : k ↦ x ^ p)) (n : ℕ)
    (D : ScalarExtension p k (WittVector p k) (p : WittVector p k) n) :
    LatticeComparison p k n D

/-- The unramified lattice model over a perfect field: for a prime $p$, a perfect field $k$ of
characteristic $p$ (its Frobenius $x ↦ x^p$ is bijective) and $n ∈ ℕ$, an `UnramifiedModel`: a
scalar extension, along maps of perfect $k$-algebras $R$, of the lattices in
$(W(R) ⊗_{W(k)} W(k))[1/p]^n$, a transport of these lattices to $W(R)$-lattices in $W(R)[1/p]^n$ for
it (`LatticeComparison`), and an action of the invertible $n × n$ matrices over
$(W(R) ⊗_{W(k)} W(k))[1/p]$ on these lattices, with a standard lattice (`MatrixAction`). -/
public def_wanted unramifiedLatticeFunctor
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (perfect : Function.Bijective (fun x : k ↦ x ^ p)) (n : ℕ) :
    UnramifiedModel p k n

/-- Ind-representability of the Witt vector affine Grassmannian (Zhu, Theorem 1.4): let $p$ be a
prime, $k$ a field of characteristic $p$, `C` coefficient data making the domain $B$ a $π$-adically
complete discrete valuation ring, finite over $W(k)$, with uniformizer $π$ and perfect residue field
identified with $k$, and $G$ a reductive group scheme over $B$. Then the fpqc quotient sheaf
$LG/L^+G$ on perfect $k$-algebras is the colimit of an increasing sequence of perfect spaces, each
the perfection of an algebraic space with a proper model, joined by closed maps
(`GrassmannianGeometry`). -/
public def_wanted reductiveGrassmannianGeometry
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (B : Type) [CommRing B] [IsDomain B] [Algebra (WittVector p k) B] (pi : B)
    (C : CoefficientData p k B pi)
    (G : Over (Spec (.of B))) [GrpObj G] [IsReductive (Spec (.of B)) G] :
    GrassmannianGeometry p k B pi G

/-- Convolution on the Witt vector affine Grassmannian (Zhu, §1.4): let $p$ be a prime, $k$ a field
of characteristic $p$, `C` coefficient data making the domain $B$ a $π$-adically complete discrete
valuation ring, finite over $W(k)$, with uniformizer $π$ and perfect residue field identified with
$k$, $G$ a reductive group scheme over $B$, and `M` a presentation of the fpqc quotient $LG/L^+G$ as
the colimit of an increasing sequence of perfect spaces with closed transition maps
(`GrassmannianGeometry`). Then the twisted product $LG ×^{L^+G} LG/L^+G$ has such a presentation,
with maps from its stages to stages of `M` that are perfections of proper maps of the ordinary
models, compatible with the transitions and inducing the convolution map
$LG ×^{L^+G} LG/L^+G → LG/L^+G$ (`ConvolutionGeometry`). -/
public def_wanted reductiveConvolutionGeometry
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (B : Type) [CommRing B] [IsDomain B] [Algebra (WittVector p k) B] (pi : B)
    (C : CoefficientData p k B pi)
    (G : Over (Spec (.of B))) [GrpObj G] [IsReductive (Spec (.of B)) G]
    (M : GrassmannianGeometry p k B pi G) : ConvolutionGeometry p k B pi G M

end WantedExt.AlgebraicGeometry.RelativeWittSourceComparisons
