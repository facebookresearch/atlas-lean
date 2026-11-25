/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import MathlibExt.AlgebraicGeometry.ProjectiveSpace
public import WantedExt.AlgebraicGeometry.FaltingsHeightWanted
import all WantedExt.AlgebraicGeometry.FaltingsHeightWanted
public import WantedExt.AlgebraicGeometry.JacobianChallengeWanted
import all WantedExt.AlgebraicGeometry.JacobianChallengeWanted

/-!
# Javanpeykar's bound for the Faltings height of a Belyi curve

A Belyi map of a curve over a field is a finite morphism to the projective line that is
unramified outside $0$, $1$ and $\infty$; the Belyi degree is the least degree of such a map.
Javanpeykar bounds the Faltings height of a curve over $\overline{\mathbb{Q}}$ of genus
$g \ge 1$, the stable Faltings height of its Jacobian, polynomially in its Belyi degree.

Reference: A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra
Number Theory 8 (2014), 89–140, Theorem 1.1.1, p. 90, and §2.3,
<https://doi.org/10.2140/ant.2014.8.89> (arXiv:1403.6404v1, Theorem 1.1.1, p. 1, and §2.3,
pp. 8–9).
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.JavanpeykarBelyi

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AbelianSchemes
open MathlibExt.AlgebraicGeometry.ProjectiveSpace
open MathlibExt.AlgebraicGeometry.JacobianChallengeWanted.AlgebraicGeometry.JacobianChallenge
open WantedExt.AlgebraicGeometry.FaltingsHeight

universe u

/-- **The complement of $0$, $1$ and $\infty$ in the projective line.** For a field $k$, the open
subscheme $D_+\bigl(x_0 x_1 (x_0 - x_1)\bigr)$ of $\mathbb{P}^1_k = \operatorname{Proj}
k[x_0, x_1]$, the complement of the three points $0 = [0 : 1]$, $1 = [1 : 1]$ and
$\infty = [1 : 0]$. -/
def belyiLocus (k : Type u) [Field k] : (projectiveSpace k 1).left.Opens :=
  letI := @MvPolynomial.gradedAlgebra
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k)
    (MvPolynomial.X 0 * MvPolynomial.X 1 * (MvPolynomial.X 0 - MvPolynomial.X 1))

/-- **Belyi map.** For a field $k$ and a scheme $C$ over $k$, a morphism
$f : C \to \mathbb{P}^1_k$ over $k$ is a Belyi map if it is finite and unramified over
$\mathbb{P}^1_k \setminus \{0, 1, \infty\}$, that is, its restriction over that open subscheme is
formally unramified (a finite morphism is of finite type, so this is unramified). -/
def IsBelyiMap {k : Type u} [Field k] {C : Over (Spec (CommRingCat.of k))}
    (f : C ⟶ projectiveSpace k 1) : Prop :=
  IsFinite f.left ∧ FormallyUnramified (f.left ∣_ belyiLocus k)

/-- **Belyi map of a given degree.** For a field $k$, a scheme $C$ over $k$ and a natural number
$d$, $C$ has a Belyi map of degree $d$ if there is a Belyi map $f : C \to \mathbb{P}^1_k$ whose
rank `Scheme.Hom.finrank` is $d$ at every point of $\mathbb{P}^1_k$. -/
def HasBelyiMapOfDegree {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k))) (d : ℕ) :
    Prop :=
  ∃ f : C ⟶ projectiveSpace k 1, IsBelyiMap f ∧ ∀ y, f.left.finrank y = d

/-- **Belyi degree.** For a field $k$ and a scheme $C$ over $k$, the Belyi degree
$\deg_B(C)$ is the least $d$ such that $C$ has a Belyi map of degree $d$: the minimal degree of a
finite morphism $C \to \mathbb{P}^1_k$ unramified over $\mathbb{P}^1_k \setminus \{0, 1,
\infty\}$. It is $0$ if there is no such map; by Belyi's theorem a smooth projective connected
curve over $\overline{\mathbb{Q}}$ has a Belyi map. See A. Javanpeykar, *Polynomial bounds for
Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), §1.1, p. 90,
<https://doi.org/10.2140/ant.2014.8.89>. -/
def belyiDegree {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k))) : ℕ :=
  sInf {d | HasBelyiMapOfDegree C d}

/-- **Base change to an algebraic closure.** For a field $K$ and a scheme $C$ over $K$, the
scheme $C_{\bar K} = C \times_{\operatorname{Spec} K} \operatorname{Spec} \bar K$ over the
algebraic closure $\bar K$ of $K$. -/
abbrev overAlgebraicClosure (K : Type u) [Field K] (C : Over (Spec (CommRingCat.of K))) :
    Over (Spec (CommRingCat.of (AlgebraicClosure K))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).obj C

/-- **Jacobian of a curve as an abelian variety.** For a field $k$ and a curve $C$ over $k$
(proper, smooth of relative dimension $1$ and geometrically irreducible), the Jacobian $J(C)$
of the Jacobian challenge, with its group scheme structure, as an abelian scheme over
$\operatorname{Spec} k$: it is smooth (of relative dimension the genus), proper and geometrically
irreducible, hence geometrically connected, and commutative. -/
public def_wanted jacobian {k : Type u} [Field k] (C : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    AbelianScheme (Spec (CommRingCat.of k)) :=
  letI : GrpObj (❰Jacobian❱ C) := ❰Jacobian.instGrpObj❱
  haveI : IsProper (❰Jacobian❱ C).hom := ❰Jacobian.instIsProper❱
  haveI : GeometricallyIrreducible (❰Jacobian❱ C).hom := ❰Jacobian.instGeometricallyIrreducible❱
  haveI : SmoothOfRelativeDimension (❰genus❱ C) (❰Jacobian❱ C).hom :=
    ❰Jacobian.smoothOfRelativeDimension_genus❱
  haveI : IsCommMonObj (❰Jacobian❱ C) := ❰instIsCommMonObj❱
  { model := ❰Jacobian❱ C
    smooth := SmoothOfRelativeDimension.smooth (❰genus❱ C) _
    connected := ⟨fun _ _ y _ fst snd h => by
      have : IrreducibleSpace _ :=
        GeometricallyIrreducible.geometrically_irreducibleSpace y fst snd h
      infer_instance⟩ }

/-- **Javanpeykar's bound for the Faltings height of a Belyi curve.** Let $X$ be a smooth
projective connected curve of genus $g \ge 1$ over $\overline{\mathbb{Q}}$, and let
$h_{\mathrm{Fal}}(X)$ be its Faltings height, the stable Faltings height of its Jacobian in
Faltings' normalization. Then
$$-g \log(2\pi) \le h_{\mathrm{Fal}}(X) \le 13 \cdot 10^6 \, g \, \deg_B(X)^5,$$
where $\deg_B(X)$ is the Belyi degree of $X$.

Every such curve is defined over a number field, so the statement takes a number field $K$ and a
curve $C$ over $K$ (proper, smooth of relative dimension $1$, geometrically irreducible) of genus
$g \ge 1$, with $X = C_{\bar K}$ over the algebraic closure $\bar K$ of $K$, an algebraic
closure of $\mathbb{Q}$. Then $h_{\mathrm{Fal}}(X) = h_F(J(C))$, the genus of $X$ is that of
$C$, and the Belyi degree is computed over $\bar K$. The hypothesis that $X$ has a Belyi map is
Belyi's theorem; it makes $\deg_B(X)$ the minimum of the degrees of Belyi maps. The theorem also
bounds three further Arakelov invariants of $X$ (the self-intersection of the dualizing sheaf,
the discriminant and Faltings' delta invariant); those bounds are not part of this statement.

Source: A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra
Number Theory 8 (2014), 89–140, Theorem 1.1.1, p. 90, with $h_{\mathrm{Fal}}$ defined in §2.3,
where it is identified with the stable Faltings height of the Jacobian, and its normalization
compared with that of Gaudron and Rémond in Lemma 2.4.4, <https://doi.org/10.2140/ant.2014.8.89>
(arXiv:1403.6404v1). -/
public theorem_wanted javanpeykar_faltingsHeight_bound (K : Type u) [Field K] [NumberField K]
    (C : Over (Spec (CommRingCat.of K))) [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom]
    (hB : ∃ d, HasBelyiMapOfDegree (overAlgebraicClosure K C) d) :
    1 ≤ ❰genus❱ C →
    -(❰genus❱ C : ℝ) * Real.log (2 * Real.pi) ≤ ❰faltingsHeight❱ K (❰jacobian❱ C) ∧
      ❰faltingsHeight❱ K (❰jacobian❱ C) ≤
        13 * 10 ^ 6 * (❰genus❱ C : ℝ) * (belyiDegree (overAlgebraicClosure K C) : ℝ) ^ 5

end WantedExt.AlgebraicGeometry.JavanpeykarBelyi
