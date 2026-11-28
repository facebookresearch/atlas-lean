# Consistency and convergence rate of the BHV-penalized likelihood estimator

**Setting.** Trees $x = (\tau, q)$ with $n$ leaves (topology $\tau$, branch lengths $q$) live in Billera–Holmes–Vogtmann (BHV) tree space $\mathcal{T}$, a CAT(0) space made of orthants $\mathbb{R}_{\ge 0}^{2n-3}$ glued along faces, with geodesic distance $d$. Sequence data $\mathbf{Y}_k$ of $k$ independent sites are generated under an identifiable substitution model ($P_{\tau,q} = P_{\tau',q'}$ iff $(\tau,q) = (\tau',q')$) on a true resolved tree $x^* = (\tau^*, q^*)$ whose pendant-edge lengths are at least $e$, inner-edge lengths at least $f$, and all lengths at most $g$, with $e, g$ known. Let $\ell_k$ be the log-likelihood and $\phi(x)$ the expected per-site log-likelihood, so $\phi(x^*) - \phi(x) = \mathrm{KL}(P_{x^*}, P_x)$.

**Estimator.** Given a reference (e.g. species) tree $x^\circ$ and $\alpha_k > 0$,

$$
\hat x_k = (\hat\tau_k, \hat q_k) \in \operatorname*{argmin}_{x \in \mathcal{T}_{e,g}} \Big\{ -\tfrac1k \ell_k(x) + \alpha_k\, d(x, x^\circ)^2 \Big\},
$$

a ridge-type penalty pulling the gene tree toward $x^\circ$; a minimizer exists.

**Theorem.**

1. *(Consistency.)* If $\alpha_k \to 0$ and $\alpha_k = \Omega(\log k/\sqrt{k})$, then $\hat x_k \to x^*$ almost surely.
2. *(Global error bound.)* By the Łojasiewicz inequality there are an integer $m \ge 2$, a neighbourhood $U$ of $x^*$ and $C_n > 0$ with $\phi(x^*) - \phi(x) \ge C_n\, d(x^*, x)^m$ on $U$. Then for every $\delta > 0$ there is a constant $C$ (depending on $n, \delta, e, g, m, x^*, x^\circ$) such that with probability at least $1 - \delta$

$$
d(x^*, \hat x_k) \le C \Big( \frac{\log k}{\alpha_k \sqrt{k}} + \alpha_k^{1/(m-1)} \Big)^{1/2};
$$

   choosing $\alpha_k$ optimally gives $d(x^*, \hat x_k) = O\big(\log k / k^{1/(4m)}\big)$.
3. *(Jukes–Cantor.)* Under the Jukes–Cantor model the bound holds with $m = 2$ and explicit constants polynomial in $n$ (with exponents depending on $g$ and $f$), and for $0 < \nu < 1/4$ a sequence length $k$ of order $\big[f^{-2} n^4 \operatorname{polylog} + \beta(n,g,f)^2 f^{-2}\big]^{4/(1 - 4\nu)}$ suffices to recover the topology $\tau^*$ with probability at least $1 - \delta$; with $f$ replaced by any $t_0 > 0$, the estimator recovers every edge longer than $t_0$.

## Proof depends on

- [The space of phylogenetic trees is CAT(0)](../../../../not-yet-classified/phylogenetic-tree-space/tree-space-is-cat0.md)

## Expansion

The penalty $R(x) = d(x, x^\circ)^2$ is strongly convex along BHV geodesics (BHV space is CAT(0)), which supplies the curvature needed for a variational source condition of Hofmann type: $-\langle \text{subgradient of } R, x - x^*\rangle \le \tfrac12 D(x^*, x) + \beta(\phi(x^*) - \phi(x))^{1/m}$. A uniform deviation bound $\sup_x |\tfrac1k \ell_k(x) - \phi(x)| = O(\log k/\sqrt{k})$ over $\mathcal{T}_{e,g}$ gives the first term of the error bound, and the Łojasiewicz exponent converts excess KL risk into distance, giving the $\alpha_k^{1/(m-1)}$ bias term. Phylogenetics is non-standard because $\mathcal{T}$ is not a smooth space (it is a union of orthants glued along faces) and the likelihood is only piecewise analytic, which is why these rates are slower than the parametric $k^{-1/2}$.

## Sources

- V. Dinh, L. S. T. Ho, M. A. Suchard, F. A. Matsen IV, "Consistency and convergence rate of phylogenetic inference via regularization", arXiv:1606.03059 (2016): Section 2 (BHV space, Assumptions 2.1–2.2, the penalized estimator and its existence lemma), Section 3 (Definition 3.1 and the lemma that the BHV geodesic distance is strongly convex), Theorem 5.1 and Corollary 5.1 (consistency), Section 5.2 (Łojasiewicz regularity, Theorem 5.2, Corollary 5.2), Section 6 (Theorems 6.1–6.3, Jukes–Cantor). <https://doi.org/10.48550/arXiv.1606.03059> Published version: The Annals of Statistics 46 (2018) 1481–1512, <https://doi.org/10.1214/17-aos1592>.
