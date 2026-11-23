# Wald–Wolfowitz theorem: optimality of the SPRT

Let $P_0$ and $P_1$ be mutually absolutely continuous probability measures on a measurable space $\mathcal{X}$ ($P_1 \ll P_0$ and $P_0 \ll P_1$), and let the observations $X_1, X_2, \dots$ be the coordinates of $\omega \in \mathcal{X}^{\mathbb{N}}$, $X_{i+1}(\omega) = \omega_i$. Write $L = dP_1/dP_0$ (a real number almost everywhere) and $\Lambda_n = \sum_{i=1}^n \log L(X_i)$. Assume $P_0 \ne P_1$ and consider the [SPRT](sprt-time.md) with log-boundaries $a < 0 < b$ and stopping time $N$. Let $(T, D)$ be any test: a stopping time $T$ of the observations with $\mathbb{E}_0[T] < \infty$ and $\mathbb{E}_1[T] < \infty$, and a rejection region $D$ for $P_0$ in the stopped σ-algebra $\mathcal{F}_T$, whose error probabilities do not exceed those of the SPRT:

$$P_0^{\otimes \mathbb{N}}(D) \le P_0^{\otimes \mathbb{N}}(N < \infty,\ \Lambda_N \ge b), \qquad P_1^{\otimes \mathbb{N}}(D^c) \le P_1^{\otimes \mathbb{N}}(N < \infty,\ \Lambda_N \le a).$$

Then the SPRT has no larger expected sample size under either hypothesis:

$$\mathbb{E}_0[N] \le \mathbb{E}_0[T], \qquad \mathbb{E}_1[N] \le \mathbb{E}_1[T],$$

where $\mathbb{E}_j$ is the expectation under $P_j^{\otimes \mathbb{N}}$. This is the Wald–Wolfowitz theorem (1948) as stated in Lai 2001, §2, p. 305, for non-randomised tests; randomised tests are not covered by this statement.

The expected sample sizes are integrals in $[0, \infty]$, so the statement does not presuppose that the SPRT stops in finite expected time.

## Sources

- T. L. Lai, *Sequential analysis: some classical problems and new challenges*, Statistica Sinica 11 (2001) 303–408, §2, p. 305 (statement of the Wald–Wolfowitz theorem, with reference to A. Wald and J. Wolfowitz, *Optimum character of the sequential probability ratio test*, Ann. Math. Statist. 19 (1948) 326–339; original not consulted, statement as given in Lai 2001).
- B. Eisenberg, *Sequential probability ratio test*, Encyclopedia of Mathematics (online), equations (a1)–(a3), the paragraph after (a3).

## Background

- [Optimal stopping and the Snell envelope](../../martingales/optimal-stopping-and-the-snell-envelope/README.md): the variational problem is associated with a Bayesian optimal stopping problem (Peskir and Shiryaev, *Optimal Stopping and Free-Boundary Problems*, 2006, Introduction (B), solved there for the Wiener process in §21).
- [Neyman–Pearson lemma](../neyman-pearson-dominated-two-simple.md): the fixed-sample-size optimality that the Wald–Wolfowitz theorem extends to sequential tests.
