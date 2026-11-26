# Renewal equation and generation series for the mean of a multivariate Hawkes epidemic

**Setting.** Use the multivariate Hawkes process of the companion entry: type-$i$ intensity $\lambda^0_i(t)+\sum_j\int_{[0,t)}\phi^j_i(t-u)N_j(\mathrm du)$, with $\widetilde N^{j'}$ the descendants of one type-$j'$ case born at time $0$ and $\widetilde N^0=N$. Let $M^{j'}_l(t)=\mathbb E\,\widetilde N^{j'}_l(t)$, $\Phi^{j'}_l(t)=\int_0^t\phi^{j'}_l(s)\,\mathrm ds$ and $\Lambda^0_l(t)=\int_0^t\lambda^0_l(s)\,\mathrm ds$.

**Statement.** For $1\le j',l\le d$ the mean functions solve the linear Volterra (renewal) system

$$M^{j'}_l(t)=\Phi^{j'}_l(t)+\sum_{j=1}^d\int_0^tM^j_l(t-s)\,\phi^{j'}_j(s)\,\mathrm ds,$$

and the mean of the full epidemic is

$$\mathbb E N_l(t)=\Lambda^0_l(t)+\sum_{j=1}^d\int_0^tM^j_l(t-s)\,\lambda^0_j(s)\,\mathrm ds.$$

The solution, finite or infinite, is the generation series: $M^{j'}_l$ has density

$$m^{j'}_l(t)=\sum_{r\ge1}\ \sum_{k_1,\dots,k_{r-1}}\bigl(\phi^{j'}_{k_1}*\phi^{k_1}_{k_2}*\cdots*\phi^{k_{r-1}}_{l}\bigr)(t),$$

where the $r$-th term is the expected rate of type-$l$ cases in generation $r$ of the outbreak started by one type-$j'$ case. In particular, the expected final size of an outbreak started by one type-$j'$ case is $\sum_{r\ge1}(G^r)_{j'l}$ with $G_{jk}=\int_0^\infty\phi^j_k$, finite for every pair of types when the spectral radius of the next-generation matrix $G$ is below $1$.

## Depends on

- [Volterra system for the Laplace transform of a multivariate Hawkes epidemic](volterra-system-for-the-laplace-transform-of-a-multivariate-hawkes-process.md)

## Expansion

Differentiate the single-time Laplace system with respect to $a_l$ at $a=0$, using $L^j(0,t)=1$: the derivative of the exponent gives $-\Phi^{j'}_l$ from the factor $e^{-a_l}$ and $-\sum_jM^j_l*\phi^{j'}_j$ from the inner transforms, which is the renewal equation. Iterating it, or counting the expected number of descendants generation by generation in the cluster representation, gives the convolution series; a nonnegative series of this type converges to the minimal solution of the renewal equation. The source also derives the corresponding Volterra equations for second-order moments and covariance measures at one or two times, and uses them for numerical approximation schemes.

## Sources

- B. Vieille, R. Senoussi and S. Soubeyrand, *Functional Laplace Transform of a Multivariate Hawkes Process, Subsequent Characteristics, and Numerical Approximations*, arXiv:2507.15370 (2025): Section 4, Propositions 4.1 and 4.2 (first-order moments), Propositions 4.3–4.6 (second-order moments). <https://doi.org/10.48550/arXiv.2507.15370>
