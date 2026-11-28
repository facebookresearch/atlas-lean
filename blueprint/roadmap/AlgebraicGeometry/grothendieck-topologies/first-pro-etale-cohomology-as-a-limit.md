# First pro-étale cohomology with ℓ-adic coefficients as a limit

This node is still to be broken down: the statement is precise, but its proof is not.

Let $\ell$ be a prime and $X$ a scheme with
$H^0(X_{\mathrm{et}}, \mathbb{Z}/\ell^n\mathbb{Z}) = \mathbb{Z}/\ell^n\mathbb{Z}$ for every $n \ge 1$,
for instance a nonempty connected scheme. Let $\hat{\mathbb{Z}}_\ell$ be the sheaf
$U \mapsto \operatorname{Map}_{\mathrm{cont}}(U, \mathbb{Z}_\ell)$ on the pro-étale site
$X_{\text{proét}}$, and $\nu \colon X_{\text{proét}} \to X_{\mathrm{et}}$ the projection.

1. $\hat{\mathbb{Z}}_\ell = \varprojlim_n \nu^*(\mathbb{Z}/\ell^n\mathbb{Z})$, and
   $H^1(X_{\text{proét}}, \hat{\mathbb{Z}}_\ell)$ is canonically the continuous étale cohomology
   $H^1_{\mathrm{cont}}(X_{\mathrm{et}}, (\mathbb{Z}/\ell^n\mathbb{Z})_n)$, the first cohomology of
   $R\varprojlim_n R\Gamma(X_{\mathrm{et}}, \mathbb{Z}/\ell^n\mathbb{Z})$.
2. The resulting map
   $H^1(X_{\text{proét}}, \hat{\mathbb{Z}}_\ell) \to \varprojlim_n H^1(X_{\mathrm{et}}, \mathbb{Z}/\ell^n\mathbb{Z})$
   is bijective: it is surjective with kernel
   $R^1\varprojlim_n H^0(X_{\mathrm{et}}, \mathbb{Z}/\ell^n\mathbb{Z})$, which vanishes because the
   transition maps $\mathbb{Z}/\ell^{n+1}\mathbb{Z} \to \mathbb{Z}/\ell^n\mathbb{Z}$ are surjective.

So the first pro-étale cohomology with coefficients $\hat{\mathbb{Z}}_\ell$ is the ℓ-adic first
cohomology $\varprojlim_n H^1(X_{\mathrm{et}}, \mathbb{Z}/\ell^n\mathbb{Z})$ of the classical theory.
For proper smooth schemes over an algebraically closed field of characteristic other than $\ell$,
the comparison in every degree is
[Integral ℓ-adic cohomology is the limit of its finite levels](../not-yet-classified/comparison-bijective.md).

## Expansion

This node is still to be broken down. A good expansion states and links:

- the sheaf of continuous maps to a topological space on $X_{\text{proét}}$ (Bhatt–Scholze, Lemma
  4.2.12), and the identity $\hat{\mathbb{Z}}_\ell = \varprojlim_n \nu^*(\mathbb{Z}/\ell^n\mathbb{Z})$
  (their Lemma 6.8.2 (1), for $E = \mathbb{Q}_\ell$);
- their Proposition 5.6.2: for a pro-system $(F_n)$ of abelian sheaves on $X_{\mathrm{et}}$ with
  surjective transition maps,
  $H^i_{\mathrm{cont}}(X_{\mathrm{et}}, (F_n)) \cong H^i(X_{\text{proét}}, \varprojlim \nu^* F_n)$,
  with its proof, which writes the left side as the cohomology of
  $R\varprojlim R\Gamma(X_{\mathrm{et}}, F_n)$;
- the short exact sequences
  $0 \to R^1\varprojlim_n H^{p-1}(K_n) \to H^p(R\varprojlim K) \to \varprojlim_n H^p(K_n) \to 0$
  (Stacks Project, Tag 07KY) and the vanishing of $R^1\varprojlim$ on Mittag-Leffler systems (Tag
  07KW).

## Depends on

- [Continuous Module Sheaf](../not-yet-classified/continuous-adic-coefficients/continuous-module-sheaf.md),
  for the sheaf $\hat{\mathbb{Z}}_\ell$, the sheaf $U \mapsto C(U, M)$ on the small pro-étale site for
  $M = \mathbb{Z}_\ell$
- [Cohomology](../not-yet-classified/pro-etale-cohomology-functoriality/cohomology.md), for the
  cohomology $H^1(X_{\text{proét}}, -)$ of a sheaf of modules on the small pro-étale site

## Sources

- B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, arXiv:1309.1198v2, <https://arxiv.org/abs/1309.1198v2>: Lemma 4.2.12, p. 30; Proposition 5.6.2 and its proof, p. 41; Lemma 6.8.2 (1) and its proof,
  pp. 58–59. Published in Astérisque 369 (2015), 99–201 (the published version not read; the page
  numbers above are those of the arXiv version).
- The Stacks Project, Tag 07KY (Lemma 15.88.10), <https://stacks.math.columbia.edu/tag/07KY>, and Tag
  07KW (Lemma 15.88.1), <https://stacks.math.columbia.edu/tag/07KW>.
