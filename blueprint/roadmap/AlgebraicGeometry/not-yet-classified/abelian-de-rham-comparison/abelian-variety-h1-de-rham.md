# $H^1$ of an abelian variety is de Rham with Hodge–Tate weights in $\{0, 1\}$

Let $F$ be a
finite extension of $\mathbb{Q}_p$ inside $\overline{\mathbb{Q}}_p$ and let $A/F$ be an abelian
variety of dimension $g$: a commutative group object over $\operatorname{Spec} F$ that is proper,
geometrically connected and smooth of relative dimension $g$. Let
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
the sheaf of continuous $\mathbb{Q}_p$-valued functions. The Galois group acts on
$B_{\mathrm{dR}}^+$ through its action on $\mathcal{O}_{\mathbb{C}_p}$ by functoriality of
$B_{\mathrm{dR}}^+$ (`PadicComplexInt.galoisBDeRhamPlus`).

Peter Scholze, *p-adic Hodge theory for rigid-analytic varieties*, Forum Math. Pi 1 (2013), e1,
[Corollary 1.8, pp. 5–6](https://doi.org/10.1017/fmp.2013.1): for a proper smooth rigid-analytic
variety $X$ over $F$, $H^i(X_{\bar F, \mathrm{et}}, \mathbb{Q}_p)$ is de Rham with associated
filtered $F$-vector space $H^i_{\mathrm{dR}}(X)$. It applies to the analytification of $A$ by
Theorems 9.1 and 9.3, pp. 74–75 (coherent and étale cohomology of a proper scheme and of its
analytification agree); the corrigendum, Forum Math. Pi 4 (2016), e6,
<https://doi.org/10.1017/fmp.2016.4>, keeps these results. For $i = 1$ the Hodge filtration of
$H^1_{\mathrm{dR}}(A/F)$ has $\operatorname{Fil}^0 = H^1_{\mathrm{dR}}(A/F)$,
$\operatorname{Fil}^1 = H^0(A, \Omega^1_A)$, of dimension $g$, and $\operatorname{Fil}^2 = 0$.
