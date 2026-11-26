# Central limit theorems for pair occupation times of the voter model in dimensions three and four

**Setting.** Let $(\eta_t)$ be the voter model on $\mathbb Z^d$ (each site at rate $1$ copies a uniformly chosen nearest neighbour), started from its non-trivial invariant law $\nu_p$, $p \in (0, 1)$, obtained as the limit from Bernoulli($p$) product measure. Let $\Phi(x)$ be the probability that simple random walk started at $x$ ever hits $\mathbf 0$ (so $\Phi(\mathbf 0) = 1$), $\gamma_d = \Phi(e_1)$ its return probability, and $\chi(p, d) = 2p(1 - p)(1 - \gamma_d)$. By duality with coalescing random walks,

$$\alpha_{\mathbf 0, x}(p) := \mathbb E_{\nu_p}[\eta_t(\mathbf 0)\eta_t(x)] = p\,\Phi(x) + p^2\bigl(1 - \Phi(x)\bigr).$$

The quadratic additive functional is $\xi^{\mathbf 0, x}_t = \int_0^t \eta_s(\mathbf 0)\eta_s(x)\,ds$, the time both sites hold opinion $1$.

**Theorem.**
1. *($d = 4$.)* For fixed $x \in \mathbb Z^4$ and $T > 0$,

$$\left\{\frac{\xi^{\mathbf 0, x}_{tN} - tN\alpha_{\mathbf 0, x}(p)}{\sqrt{N\log N}}\right\}_{0 \le t \le T} \Longrightarrow \{C_4(x) B_t\}_{0 \le t \le T}, \qquad C_4(x) = \sqrt{\frac{\chi(p, 4)}{2\pi^2}}\,\bigl(\Phi(x) + 2(1 - \Phi(x))p\bigr),$$

in $C[0, T]$, with $B$ a standard Brownian motion. For $x = \mathbf 0$ this is the occupation-time invariance principle.
2. *($d = 3$.)* For $u \in \mathbb R^3 \setminus \{\mathbf 0\}$, with $u_N$ the nearest point of $\mathbb Z^3/\sqrt N$ to $u$,

$$\left\{\frac{\xi^{\mathbf 0, \sqrt N u_N}_{tN} - tN\alpha_{\mathbf 0, \sqrt N u_N}(p)}{N^{3/4}}\right\}_{0 \le t \le T} \Longrightarrow \{C_3\zeta^u_t\}_{0 \le t \le T}, \qquad C_3 = \sqrt{6(1 - \gamma_3)p^3(1 - p)},$$

where $\zeta^u$ is a centred continuous Gaussian process whose covariance is an explicit integral of the heat kernel $f^3_s$ of three-dimensional Brownian motion at $\mathbf 0$ and at $u$; it is not a Brownian motion.

## Depends on

- [Coalescing random walks dual to the voter model on a finite graph](../../coalescent-theory/structured-coalescent/coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

The proof writes the centred functional as a martingale plus a remainder via the resolvent of the generator and computes the quadratic variation approximately, using duality to reduce correlations of $\eta$ to meeting probabilities of coalescing walks. In $d = 4$ the walk is barely transient: the expected number of meetings of two lineages up to time $N$ grows like $\log N$, giving the $\sqrt{N\log N}$ normalization and Brownian limit, and the pair functional only rescales the variance through $\Phi(x)$. In $d = 3$ correlations decay like $|x|^{-1}$, so the variance grows like $N^{3/2}$ and the limit retains long memory; placing the second site at distance $\sqrt N u$ makes the two sites' occupation times interact through the heat kernel at $u$.

## Sources

- X. Xue, "CLT for quadratic additive functionals of three-dimensional and four-dimensional voter models", arXiv:2610.36594 (2026), Proposition 2.1, Theorems 2.2 and 2.3, <https://doi.org/10.48550/arXiv.2610.36594>.
