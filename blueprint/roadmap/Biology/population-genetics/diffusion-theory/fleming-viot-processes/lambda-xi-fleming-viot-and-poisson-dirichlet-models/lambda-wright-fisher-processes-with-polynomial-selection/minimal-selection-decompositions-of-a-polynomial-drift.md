# Minimal selection decompositions of a polynomial drift

**Setting.** Let $d$ be a polynomial with $d(0)=d(1)=0$ and $\deg d\le m$, and let $\mathcal S_d$ be its set of selection decompositions $(\beta,p)$, i.e. Moran-type interaction rates $\beta=(\beta_\ell)_{\ell=2}^m\in\mathbb{R}_+^{m-1}$ and colouring rules $p$ with $d(x)=\sum_{\ell}\beta_\ell\sum_{i=0}^{\ell}b_{i,\ell}(x)(p_{i,\ell}-i/\ell)$, where $b_{i,\ell}$ is the Bernstein basis. Each decomposition is a potential genealogy (ancestral selection graph) for the same forward Λ-Wright–Fisher process. Its effective branching rate is $b(\beta)=\sum_{\ell=2}^m\beta_\ell(\ell-1)$. Write $\rho(f)\in\mathbb{R}^{m-1}$ for the inner coefficients of the degree-$m$ Bernstein expansion of a polynomial $f$ vanishing at the boundary, $f=\sum_{i=1}^{m-1}\rho_i(f)\,b_{i,m}$, and let

$$
\mathcal S_\lambda=\bigl\{\rho(d_{\beta,p}) : b(\beta)=\lambda\bigr\}\subset\mathbb{R}^{m-1}
$$

be the set of $\lambda$-decomposable vectors.

**Definitions.** A decomposition $(\beta,p)\in\mathcal S_d$ is *$b$-minimal* if $b(\beta)=b_\star(d):=\inf_{(\beta',p')\in\mathcal S_d}b(\beta')$. A *thinning mechanism* is a lower-triangular stochastic matrix $\mathbb T=(\mathbb T_{k,i})_{k,i}$, acting by $(\mathbb T\beta)_\ell=\sum_{k\ge\ell}\beta_k\mathbb T_{k,\ell}$; $(\beta,p)$ is *graph-minimal* if the identity is the only thinning $\mathbb T$ for which $(\mathbb T\beta,p')\in\mathcal S_d$ for some colouring rule $p'$.

**Results.**

1. (Scaling) For every $\lambda>0$, $\mathcal S_\lambda$ is a polytope and $\mathcal S_\lambda=\lambda\,\mathcal S_1$; in particular $\mathcal S_\lambda\subseteq\mathcal S_{\lambda'}$ for $\lambda'\ge\lambda$.
2. (Existence) Every such $d$ has a $b$-minimal selection decomposition, and

$$
b_\star(d)=\inf\{\lambda>0:\ \rho(d)\in\lambda\,\mathcal S_1\}.
$$

3. Every $b$-minimal selection decomposition is graph-minimal.
4. If $\deg d=3$, then for every $(\beta,p)\in\mathcal S_d$ with $b(\beta)>b_\star(d)$ there is a thinning $\mathbb T\ne\mathrm{Id}$ and a colouring rule $p'$ such that $(\mathbb T\beta,p')\in\mathcal S_d$ is $b$-minimal.

## Depends on

- [Bernstein duality for Λ-Wright–Fisher processes with polynomial selection](bernstein-duality-for-lambda-wright-fisher-processes-with-polynomial-selection.md)

## Expansion

Because the leaf process of the ancestral selection graph is positive recurrent when $b(\beta)<c(\Lambda)$ and transient when $b(\beta)>c(\Lambda)$, minimizing $b(\beta)$ over all genealogies compatible with the same drift identifies the most economical backward structure: the drift $d$ admits a positive recurrent ancestral graph whenever $b_\star(d)<c(\Lambda)$. Linearity of $(\beta,p)\mapsto\rho(d_{\beta,p})$ in the rescaled variables gives the polytope structure and the homogeneity $\mathcal S_\lambda=\lambda\mathcal S_1$, so $b_\star(d)$ is the gauge of $\rho(d)$ with respect to $\mathcal S_1$. Thinning removes potential parents from interaction events; a $b$-minimal decomposition cannot be thinned further since any proper thinning strictly lowers the effective branching rate. In degree three the converse direction holds: every non-minimal decomposition thins to a minimal one, recovering classical ancestral structures as minimal ones.

## Sources

- Fernando Cordero, Sebastian Hummel and Emmanuel Schertzer, "General selection models: Bernstein duality and minimal ancestral structures", *Ann. Appl. Probab.* 32(3) (2022), 1499–1556. <https://doi.org/10.1214/21-AAP1683>
- Preprint version (the locators in this item follow its numbering): Fernando Cordero, Sebastian Hummel, Emmanuel Schertzer, *General selection models: Bernstein duality and minimal ancestral structures*, arXiv (2019). Definitions 2.30, 2.31, 2.34, 2.35; Proposition 2.32; Theorem 2.36; Proposition 2.37; Proposition 3.1 (scaling property). <https://doi.org/10.48550/arXiv.1903.06731>
