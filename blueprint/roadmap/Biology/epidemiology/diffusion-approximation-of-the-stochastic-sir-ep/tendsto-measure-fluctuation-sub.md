# Diffusion approximation for the stochastic SIR epidemic

Let $\mu$ be a finite measure on $\Omega$ and $\beta, \gamma \ge 0$, let $(s, i, r)$ be a
[solution of the SIR system](../kermack-mckendrick-sir-model/is-solution.md) with transmission rate
$\beta$, removal rate $\gamma$ and population size $1$ (in densities), and $x(t) = (s(t), i(t))$.
Let $X_N(\omega) : \mathbb{R} \to \mathbb{R}^2$ ($N \in \mathbb{N}$, $\omega \in \Omega$) be
density paths, each measurable as a function of time, $U_0 : \Omega \to \mathbb{R}^2$ measurable,
$M(\omega)$ paths continuous on $[0, T]$ whose values $\omega \mapsto M(\omega)(t)$ are
measurable, and, for every $\omega$,
$U(\omega)$ the [fluctuation path](is-fluctuation-path.md) driven by $M(\omega)$ from $U_0(\omega)$
around $x$. Write $U_N = \sqrt N (X_N - x)$ for the [scaled fluctuation](fluctuation.md) and $M_N$
for the [scaled compensated increment](scaled-martingale.md), with the sup norm
$\|h\| = \max(|h_1|, |h_2|)$ on $\mathbb{R}^2$. Assume that for every $\delta > 0$, as
$N \to \infty$,

- (law of large numbers)
  $\mu\{\omega : \exists\, t \in [0, T],\ \|X_N(t) - x(t)\| \ge \delta\} \to 0$;
- (initial fluctuations) $\mu\{\omega : \|U_N(0) - U_0\| \ge \delta\} \to 0$;
- (martingale central limit theorem, coupled form)
  $\mu\{\omega : \exists\, t \in [0, T],\ \|M_N(t) - M(t)\| \ge \delta\} \to 0$.

Then the scaled fluctuations converge to $U$ uniformly on $[0, T]$ in measure: for every
$\varepsilon > 0$,

$$
\mu\bigl\{\omega : \exists\, t \in [0, T],\ \|U_N(t) - U(t)\| \ge \varepsilon\bigr\} \to 0
\quad (N \to \infty).
$$

The events in the hypotheses and in the conclusion are not assumed measurable, and $\mu$ is
applied to them as an outer measure. This is Kurtz's diffusion approximation (Kurtz 1971; Ethier
and Kurtz 1986, chapter 11, Theorem 2.3), with the law of large numbers and the martingale central
limit theorem as hypotheses.
