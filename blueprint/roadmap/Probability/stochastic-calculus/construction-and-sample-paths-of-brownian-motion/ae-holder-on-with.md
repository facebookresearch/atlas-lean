# Hölder continuity of Brownian paths

Let $B$ be a real Brownian motion, $0 \le \alpha < 1/2$ and $T \ge 0$. Then almost surely the path
$t \mapsto B_t$ is $\alpha$-Hölder continuous on $[0, T]$: there is $C \ge 0$ with
$|B_s - B_t| \le C |s - t|^\alpha$ for all $s, t \in [0, T]$. The proof applies Kolmogorov's lemma to the
moments $\mathbb E |B_t - B_s|^\beta = c_\beta |t - s|^{\beta/2}$.

## Informally uses

- [Almost sure Hölder bound on the dyadic rationals](../kolmogorov-continuity-theorem/kolmogorov-ae-holder-on-dyadics.md):
  Kolmogorov's lemma with exponents $\beta$ and $1 + \kappa = \beta/2$ gives a Hölder bound of every order
  $< \kappa/\beta = 1/2 - 1/\beta$ on the dyadic times, and $\beta$ is arbitrary.
- [Scaling of the absolute moments of a centered Gaussian](integral-abs-rpow-gaussian-real.md):
  the moment bound $\mathbb E |B_t - B_s|^\beta = c_\beta |t - s|^{\beta/2}$ that Kolmogorov's lemma needs.

## Background

- [Existence of Brownian motion](exists-is-brownian-real.md): the Brownian motion, with
  continuous paths, whose Hölder regularity is quantified here; path continuity extends the bound
  from the dyadic times to all times.

## Sources

- J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in Mathematics 274, Springer, 2016, Chapter 2, section "The continuity of sample paths".
- J.-F. Le Gall, DEA lecture notes, 1994, Lemme 2.3.
