/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.AbelianDeRhamComparison

/-!
# de Rham comparison for the first cohomology of an abelian variety over a p-adic field

For a finite extension `F` of `ℚ_p` inside `\bar{ℚ}_p` and an abelian variety `A/F` of dimension
`g`, the `Gal(\bar{ℚ}_p/F)`-representation `V = H¹_ét(A_{\bar{ℚ}_p}, ℚ_p)` is de Rham, the jumps of
the Hodge filtration on `D_dR(V)` lie in `{0, 1}`, and `dim_F Fil¹ D_dR(V) = g`.

The period ring is Mathlib's `B_dR^+ = BDeRhamPlus 𝓞_ℂ_[p] p`, the `(ker θ)`-adic completion of
`W(𝓞_ℂ_p^♭)[1/p]`, with `Fil^j B_dR^+` the kernel of the projection to
`W(𝓞_ℂ_p^♭)[1/p] ⧸ (ker θ)^j`. The Galois actions, the `ℚ_p`-structure of `B_dR^+` and the groups
`Fil^j D_dR(V) = (Fil^j B_dR^+ ⊗ V)^{G_F}`, `j ≥ 0`, are defined in
`MathlibExt.AlgebraicGeometry.AbelianDeRhamComparison`; de Rham with jumps in `{0, 1}` is then a
statement about their dimensions. The Galois group acts on `B_dR^+` by continuity because its action
on `W(𝓞_ℂ_p^♭)[1/p]` preserves `ker θ`, recorded here as a wanted theorem together with the
`p`-adic completeness of `𝓞_ℂ_p`.

Reference: Peter Scholze, *p-adic Hodge theory for rigid-analytic varieties*, Forum Math. Pi 1
(2013), e1, Corollary 1.8, pp. 5–6, with Theorems 9.1 and 9.3, pp. 74–75.
https://doi.org/10.1017/fmp.2013.1
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AbelianDeRhamComparison

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.HodgeTateComparison
open MathlibExt.AlgebraicGeometry.AbelianDeRhamComparison

variable (p : ℕ) [Fact p.Prime]

/- The ring of integers `𝓞_ℂ_p = {x : ‖x‖ ≤ 1}` of `ℂ_p` is `p`-adically separated and complete,
since `p ^ n 𝓞_ℂ_p = {x : ‖x‖ ≤ p ^ (-n)}` and `ℂ_p` is complete. This is the case `C = ℂ_p` of
`WantedExt.AlgebraicGeometry.PDivisibleHodgeTateRealization.integers_adic_complete`, stated for
Mathlib's `𝓞_ℂ_[p]`, whose `p`-adic completeness `BDeRhamPlus` takes as an instance. -/
public instance_wanted padicComplexInt_isAdicComplete :
    IsAdicComplete (Ideal.span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]

set_option linter.concreteInstances false in
/-- **Galois equivariance of Fontaine's $\theta$.** Let
$\sigma \in \operatorname{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ act on
$\mathcal{O}_{\mathbb{C}_p}$ through its continuous extension to $\mathbb{C}_p$, on
$\mathcal{O}_{\mathbb{C}_p}^\flat =
\varprojlim_{x \mapsto x^p} \mathcal{O}_{\mathbb{C}_p}/p$ coordinatewise, and on
$W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p]$ by functoriality of Witt vectors and localization. Then
$\sigma$ maps the kernel of Fontaine's map
$\theta \colon W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p] \to \mathcal{O}_{\mathbb{C}_p}[1/p]$ into
itself, so it extends by continuity to the $(\ker\theta)$-adic completion $B_{\mathrm{dR}}^+$.

J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations*, book draft (PDF of
2022-05-26), Lemma 6.9, p. 139 ($\theta$ commutes with the Galois action) and §6.2.2, p. 140 (its
extension to $W(R)[1/p]$ is equivariant), archived at
<http://web.archive.org/web/20261014003209/http://staff.ustc.edu.cn/~yiouyang/galoisrep.pdf>. -/
public theorem_wanted thetaKer_le_comap_preDeRhamGalois (σ : Galois p) :
    thetaKer p ≤ (thetaKer p).comap (preDeRhamGalois p σ)

set_option linter.concreteInstances false in
/-- **de Rham comparison for $H^1$ of an abelian variety.** Let $F$ be a finite extension of
$\mathbb{Q}_p$ inside $\overline{\mathbb{Q}}_p$ and let $A/F$ be an abelian variety of dimension
$g$: a commutative group object over $\operatorname{Spec} F$ that is proper, geometrically
connected and smooth of relative dimension $g$. Let
$V = H^1_{\mathrm{et}}(A_{\overline{\mathbb{Q}}_p}, \mathbb{Q}_p)$, on which
$\sigma \in G_F = \operatorname{Gal}(\overline{\mathbb{Q}}_p/F)$ acts by inverse image along
$\mathrm{id}_A \times \operatorname{Spec} \sigma$. Then $V$ is finite-dimensional and de Rham, the
jumps of the Hodge filtration on $D_{\mathrm{dR}}(V)$ lie in $\{0, 1\}$, and
$\dim_F \operatorname{Fil}^1 D_{\mathrm{dR}}(V) = g$.

Here $B_{\mathrm{dR}}^+$ is the $(\ker\theta)$-adic completion of
$W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p]$, $\operatorname{Fil}^j B_{\mathrm{dR}}^+$ is the kernel
of its projection to $W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p]/(\ker\theta)^j$ (that is,
$t^j B_{\mathrm{dR}}^+$), and
$D^j = (\operatorname{Fil}^j B_{\mathrm{dR}}^+ \otimes_{\mathbb{Q}_p} V)^{G_F}$ for $j \ge 0$.
The conclusion reads: $V$ is finite-dimensional,
$\dim_{\mathbb{Q}_p} D^0 = [F : \mathbb{Q}_p] \dim_{\mathbb{Q}_p} V$,
$\dim_{\mathbb{Q}_p} D^1 = [F : \mathbb{Q}_p]\, g$, and $D^2 = 0$. Since
$D_{\mathrm{dR}}(V) = (B_{\mathrm{dR}} \otimes_{\mathbb{Q}_p} V)^{G_F}$ is an $F$-vector space of
dimension at most $\dim_{\mathbb{Q}_p} V$ and $D^j = \operatorname{Fil}^j D_{\mathrm{dR}}(V)$, the
first equality says that $V$ is de Rham with
$\operatorname{Fil}^0 D_{\mathrm{dR}}(V) = D_{\mathrm{dR}}(V)$, and the others say
$\dim_F \operatorname{Fil}^1 D_{\mathrm{dR}}(V) = g$ and
$\operatorname{Fil}^2 D_{\mathrm{dR}}(V) = 0$. Taking as Hodge–Tate weights the jumps $j$, counted
with multiplicity $\dim_F \operatorname{gr}^j D_{\mathrm{dR}}(V)$ (the convention in which
$\mathbb{Q}_p(1)$ has weight $-1$), $V$ has weights in $\{0, 1\}$, the weight $1$ with
multiplicity $g$. Étale cohomology with $\mathbb{Q}_p$ coefficients is the pro-étale cohomology of
the sheaf of continuous $\mathbb{Q}_p$-valued functions. The Galois action on
$B_{\mathrm{dR}}^+$ extends that on $W(\mathcal{O}_{\mathbb{C}_p}^\flat)[1/p]$, which preserves
$\ker\theta$.

Peter Scholze, *p-adic Hodge theory for rigid-analytic varieties*, Forum Math. Pi 1 (2013), e1,
[Corollary 1.8, pp. 5–6](https://doi.org/10.1017/fmp.2013.1): for a proper smooth rigid-analytic
variety $X$ over $F$, $H^i(X_{\bar F, \mathrm{et}}, \mathbb{Q}_p)$ is de Rham with associated
filtered $F$-vector space $H^i_{\mathrm{dR}}(X)$. It applies to the analytification of $A$ by
Theorems 9.1 and 9.3, pp. 74–75 (coherent and étale cohomology of a proper scheme and of its
analytification agree); the corrigendum, Forum Math. Pi 4 (2016), e6,
<https://doi.org/10.1017/fmp.2016.4>, keeps these results. For $i = 1$ the Hodge filtration of
$H^1_{\mathrm{dR}}(A/F)$ has $\operatorname{Fil}^0 = H^1_{\mathrm{dR}}(A/F)$,
$\operatorname{Fil}^1 = H^0(A, \Omega^1_A)$, of dimension $g$, and $\operatorname{Fil}^2 = 0$. -/
public theorem_wanted abelianVariety_h1_deRham
    (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F]
    (A : Over (Spec (CommRingCat.of F))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [GeometricallyConnected A.hom] (g : ℕ) [SmoothOfRelativeDimension g A.hom] :
    FiniteDimensional ℚ_[p] (H1 p F A) ∧
      Module.finrank ℚ_[p] (filDeRham p F A (❰thetaKer_le_comap_preDeRhamGalois❱ p) 0) =
        Module.finrank ℚ_[p] F * Module.finrank ℚ_[p] (H1 p F A) ∧
      Module.finrank ℚ_[p] (filDeRham p F A (❰thetaKer_le_comap_preDeRhamGalois❱ p) 1) =
        Module.finrank ℚ_[p] F * g ∧
      filDeRham p F A (❰thetaKer_le_comap_preDeRhamGalois❱ p) 2 = ⊥

end WantedExt.AlgebraicGeometry.AbelianDeRhamComparison
