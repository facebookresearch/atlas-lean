# Universality of the production rate in long random ribosome flow models

**Ribosome flow model.** An mRNA coarse-grained into $n$ sites has occupancies $x_i(t)\in[0,1]$ and transition rates $\lambda_0,\dots,\lambda_n > 0$ ($\lambda_0$ initiation, $\lambda_n$ termination):

$$\dot x_i = \lambda_{i-1}x_{i-1}(1 - x_i) - \lambda_ix_i(1 - x_{i+1}),\qquad i = 1,\dots,n,\quad x_0 :\equiv 1,\ x_{n+1} :\equiv 0.$$

From any initial condition in $[0,1]^n$ the state converges to a unique steady state $e\in(0,1)^n$, and the protein production rate $R(t) = \lambda_nx_n(t)$ converges to $R = \lambda_ne_n$, with $\lambda_ie_i(1 - e_{i+1}) = R$ for all $i$.

**Spectral representation.** Let $T_n$ be the $(n+2)\times(n+2)$ symmetric tridiagonal matrix with zero diagonal and off-diagonal entries $\lambda_0^{-1/2},\dots,\lambda_n^{-1/2}$. It is non-negative and irreducible, with Perron eigenvalue $\sigma > 0$ and Perron eigenvector $\zeta$, and

$$R = \sigma^{-2},\qquad e_i = \lambda_i^{-1/2}\sigma^{-1}\frac{\zeta_{i+2}}{\zeta_{i+1}}.$$

Consequently $R$ is concave in the rates and $\partial R/\partial\lambda_i > 0$ for every $i$. Scaling all rates by $c > 0$ scales $\sigma$ by $c^{-1/2}$ and $R$ by $c$, so $R$ is positively homogeneous of degree one and not strictly concave.

**Theorem (universality).** Let $\lambda_0,\lambda_1,\dots$ be i.i.d. copies of a random variable $X$ supported on $[\delta,\infty)$ with $\delta > 0$, and write $\|\cdot\|_\infty$ for the essential supremum. Then, almost surely,

$$\lambda_{\max}(T_n)\to 2\,\|X^{-1/2}\|_\infty\qquad\text{and}\qquad R_n\to\big(2\,\|X^{-1/2}\|_\infty\big)^{-2}\qquad (n\to\infty).$$

The limit depends on the rate distribution only through $\|X^{-1/2}\|_\infty = (\operatorname{ess\,inf}X)^{-1/2}$, the slowest rate that occurs with positive probability.

**Finite-$n$ bound.** For $\epsilon > 0$ let $a(\epsilon) = P\big(X^{-1/2}\ge\|X^{-1/2}\|_\infty - \epsilon\big)\in(0,1]$. For integers $k < n$,

$$\big(2\|X^{-1/2}\|_\infty\big)^{-2}\le R_n\le\big(2\|X^{-1/2}\|_\infty\big)^{-2}\big(1 + O(\epsilon + k^{-2})\big)$$

with probability at least $1 - \exp\!\big(-\lfloor (n-1)/k\rfloor\,a(\epsilon)^k\big)$. Convergence can be slow because $a(\epsilon)^k$ may be tiny.

## Expansion

Upper bound on $\lambda_{\max}$: a non-negative symmetric matrix has spectral radius at most its maximal row sum, and each row of $T_n$ sums to at most $2\|X^{-1/2}\|_\infty$. Lower bound: with probability one, some block of $k$ consecutive rates all lie within $\epsilon$ of the slowest essential value, so $T_n$ dominates entrywise a matrix containing $s M_k$, where $s = \|X^{-1/2}\|_\infty - \epsilon$ and $M_k$ is the path adjacency matrix of size $k+1$ with $\lambda_{\max}(M_k) = 2\cos(\pi/(k+2))$. Letting $k\to\infty$ and $\epsilon\to 0$ gives the limit. Biologically, a long chain almost surely contains a stretch of near-minimal rates; this bottleneck, not the details of the rate distribution, sets the production rate.

## Sources

- M. Margaliot, W. Huleihel, T. Tuller, *Variability in mRNA translation: a random matrix theory approach*, Scientific Reports 11 (2021), 5300, "The ribosome flow model" (Eqs. 1–5), "Main results" (Theorems 1–2, Eqs. 6–8) and proofs (Propositions 1–2). <https://doi.org/10.1038/s41598-021-84738-0> (PMCID: PMC7970873)
