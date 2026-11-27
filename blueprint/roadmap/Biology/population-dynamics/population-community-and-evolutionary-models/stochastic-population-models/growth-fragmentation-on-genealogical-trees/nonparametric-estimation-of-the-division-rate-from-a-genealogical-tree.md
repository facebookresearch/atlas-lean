# Nonparametric estimation of the division rate from a genealogical tree

**Setting.** Cells grow exponentially at individual rates $\tau_u$ and divide into two equal halves at size-dependent rate $B(x)$, with daughters' rates drawn from a Markov kernel $\rho$. This is the size-structured branching model whose mean empirical measure solves the growth-fragmentation equation. One observes the birth sizes and growth rates $(\xi_u,\tau_u)$ of $n$ connected cells $\mathcal{U}_n$ in one of two schemes:
- **full tree**: every cell of the first $N_n$ generations, with $2^{N_n}$ of order $n$;
- **sparse tree**: the first $n$ descendants along a single line of descent.

**Estimator.** With a kernel $K$ (bounded, compactly supported, with $\int x^kK(x)\,dx = \mathbf{1}_{\{k=0\}}$ for $0 \le k \le n_0$), $K_h(x) = h^{-1}K(x/h)$ and a threshold $\varpi > 0$, set

$$ \widehat B_n(y) = \frac{y}{2}\,\frac{n^{-1}\sum_{u\in\mathcal{U}_n}K_h(\xi_u - y/2)}{\Big(n^{-1}\sum_{u\in\mathcal{U}_n}\tau_{u^-}^{-1}\mathbf{1}_{\{\xi_{u^-}\le y,\ \xi_u \ge y/2\}}\Big)\vee\varpi} . $$

This is a plug-in of the identity $\nu_B(y/2) = \frac{2B(y)}{y}\mathbb{E}_{\nu_B}\big[\tau_{u^-}^{-1}\mathbf{1}_{\{\xi_{u^-}\le y,\ \xi_u\ge y/2\}}\big]$ for the invariant birth-size density $\nu_B$: kernel density estimation for the numerator, an empirical mean for the denominator.

**Theorem.** Under the model constraints of either observation scheme (growth-rate kernels with $\rho_{\min}(A) \le \rho(v,A) \le \rho_{\max}(A)$ for fixed finite measures $\rho_{\min} \le \rho_{\max}$, $\rho_{\min}(\mathcal{E}) > 0$; and $B$ in a class $\mathcal{F}^\lambda(\mathfrak{c})$, $2^\lambda > \sup\mathcal{E}/\inf\mathcal{E}$, which requires among other things $\int_0^{r/2}x^{-1}B(2x)\,dx \le L$, $\int_{r/2}^{r}x^{-1}B(2x)\,dx \ge \ell$ and polynomial growth control, with constants $\mathfrak c = (r,m,\ell,L)$ and $\mathcal E \subset [e_{\min},e_{\max}]$), let

$$\delta(\mathfrak c) = \frac{1}{1-2^{-\lambda}}\exp\Big(-(1-2^{-\lambda})\frac{m}{e_{\max}\lambda}r^\lambda\Big)\rho_{\max}(\mathcal E), \qquad \mathbb V(x) = \exp\Big(\frac{m}{e_{\min}\lambda}x^\lambda\Big),$$

and let $\gamma_{B,\mathbb V}$ be the spectral radius of $\mathcal P_B - 1\otimes\nu_B$ (with $\mathcal P_B$ the transition of the birth-size and growth-rate chain) on functions $g$ with $\sup|g|/\mathbb V < \infty$. Assume $\delta(\mathfrak c) < 1$ in the sparse tree case (the source's Assumption 3), and $\delta(\mathfrak c) < \tfrac12$ and $\sup_{B\in\mathcal F^\lambda(\mathfrak c)}\gamma_{B,\mathbb V} < \tfrac12$ in the full tree case (Assumption 4); these give the geometric ergodicity used in the proof. Take $h_n = c_0n^{-1/(2s+1)}$ and $\varpi_n \to 0$. For every $M > 0$ there are $c_0$ and $d(\mathfrak{c}) \ge 0$ such that for every $0 < s < n_0$ and every compact interval $\mathcal{D} \subset (d(\mathfrak{c}),\infty)$ with $\inf\mathcal{D} \ge r/2$,

$$ \sup_{\rho,\ B \in \mathcal{F}^\lambda(\mathfrak{c})\cap\mathcal{H}^s(\mathcal{D},M)}\mathbb{E}_\mu\Big[\|\widehat B_n - B\|^2_{L^2(\mathcal{D})}\Big]^{1/2} \lesssim \varpi_n^{-1}(\log n)^{1/2}\,n^{-s/(2s+1)}, $$

uniformly over initial laws $\mu$ with a finite second moment of the Lyapunov function.

Up to logarithmic factors this is the classical nonparametric rate $n^{-s/(2s+1)}$ for $s$-Hölder functions. It improves on the rate $n^{-s/(2s+3)}$ obtained from indirect observation of the population size distribution, where $B$ appears as the solution of an ill-posed inverse problem. The method has been applied to single-cell *Escherichia coli* lineage data.

## Depends on

- [Growth-fragmentation equation from a size-structured branching tree](growth-fragmentation-equation-from-a-size-structured-branching-tree.md)

## Expansion

The error splits into a kernel bias of order $h^s$ and stochastic terms. Variance control needs the tree observations to decorrelate. Along a lineage, the birth-size chain is geometrically ergodic, by a drift condition with Lyapunov function $\mathbb{V}$ and a minorization on a small set. On the full tree, covariance inequalities between cells whose most recent common ancestor lies far up the tree give the same $n^{-1}$ variance up to $\log n$. The threshold $\varpi_n$ keeps the denominator away from zero, at the cost of the $\varpi_n^{-1}$ factor.

## Sources

- Marie Doumic, Marc Hoffmann, Nathalie Krell and Lydia Robert, "Statistical estimation of a growth-fragmentation model observed on a genealogical tree", arXiv:1210.3240 (2012), Section 3 (observation schemes, estimator, Assumptions 2–4, Theorem 2); Sections 4 and 5, <https://doi.org/10.48550/arXiv.1210.3240>.
