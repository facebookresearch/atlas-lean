# roABP and multilinear-formula IPS lower bounds for lifted subset sum

The lifted subset-sum system $\sum_{i<j} z_{i,j} x_i x_j - \beta$ with Boolean axioms needs exponential size in roABP-$\mathrm{IPS}_{\mathrm{LIN}}$ in every variable order and quasi-polynomial size in multilinear-formula IPS, although plain subset sum has polynomial-size refutations in both systems.

**Theorem.** Let $n \ge 1$ and let $\mathbb{F}$ be a field with $\mathrm{char}(\mathbb{F}) > \binom{2n}{2}$ and $\beta \in \mathbb{F} \setminus \{0, \dots, \binom{2n}{2}\}$. Then the system

$$
\sum_{i<j} z_{i,j} x_i x_j - \beta, \qquad \vec{x}^2 - \vec{x}, \qquad \vec{z}^2 - \vec{z}
$$

in $\mathbb{F}[x_1, \dots, x_{2n}, z_1, \dots, z_{\binom{2n}{2}}]$ is unsatisfiable, and

1. any roABP-$\mathrm{IPS}_{\mathrm{LIN}}$ refutation, in any variable order, has size $\exp(\Omega(n))$;
2. any multilinear-formula-IPS refutation has size $n^{\Omega(\log n)}$;
3. for $d = o(\log n / \log \log n)$, any product-depth-$d$ multilinear-formula-IPS refutation has size $n^{\Omega((n/\log n)^{1/d}/d^2)}$ (the printed Corollary 5.15 omits the $d = o(\log n / \log \log n)$ restriction, although its proof goes through Corollary 5.14 and Raz–Yehudayoff Theorem 3.13, which require it).

**Contrast.** If $\mathrm{char}(\mathbb{F}) > n$ and $\beta \in \mathbb{F} \setminus \{0, \dots, n\}$, the plain subset-sum system $\sum_{i=1}^n x_i - \beta, \vec{x}^2 - \vec{x}$ has explicit $\mathrm{poly}(n)$-size refutations in roABP-$\mathrm{IPS}_{\mathrm{LIN}}$ and in depth-3 multilinear-formula-$\mathrm{IPS}_{\mathrm{LIN}}$.

## Proof sketch

Unsatisfiability holds because on Boolean inputs the sum is an integer in $\{0, \dots, \binom{2n}{2}\}$. By the functional lower bound method it suffices to lower-bound every polynomial agreeing with $1/(\sum_{i<j} z_{i,j} x_i x_j - \beta)$ on the cube. Pushing the $\vec{z}$ variables into the fraction field, the tight degree bound for $1/(\sum_i x_i - \beta)$ lifts to a coefficient-dimension lower bound of $2^n$ across any balanced partition of the $\vec{x}$ variables; this gives width $2^n$ for roABPs in every order, and, through the Raz and Raz-Yehudayoff lower bounds for full-rank polynomials, the multilinear-formula bounds. For multilinear formulas the lower bound covers full IPS because multilinear refutations are automatically linear in the single non-Boolean placeholder. The subset-sum upper bound uses that $p(t) = \prod_{k=0}^n (t - k)$ vanishes on $\sum_i x_i$ over the cube while $p(\beta) \ne 0$.

## Depends on

- [Linear and circuit-restricted Ideal Proof Systems](linear-and-restricted-ideal-proof-systems.md)

## Proof depends on

- [Functional lower bound method for linear IPS](functional-lower-bound-method.md)

## Sources

- Michael A. Forbes, Amir Shpilka, Iddo Tzameret, Avi Wigderson, "Proof complexity lower bounds from algebraic circuit complexity", *Theory of Computing* 17(10), 2021, https://doi.org/10.4086/toc.2021.v017a010 (extended abstract *CCC 2016*, LIPIcs 50, https://doi.org/10.4230/LIPIcs.CCC.2016.32; arXiv:1606.05050v1; Theorem 3.13, Corollaries 5.14 and 5.15, Corollary 4.18 and Proposition 4.19).
