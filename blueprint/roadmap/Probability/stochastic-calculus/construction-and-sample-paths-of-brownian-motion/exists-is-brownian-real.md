# Existence of Brownian motion

There are a probability measure $\mu$ on the path space $\mathbb{R}^{[0, \infty)}$ and a process $W$ on it
that is a Brownian motion: its finite-dimensional laws are the Brownian ones ($W_0 = 0$ almost surely,
independent centered Gaussian increments with variance the length of the time interval), and almost every
path is continuous.

Le Gall's ENS notes build $B_t$ as the Gaussian white-noise series $\sum_h \langle \mathbf 1_{[0,t]}, h \rangle N_h$
over the Haar basis and get continuity from the uniform convergence of that series. Another route
realises the Brownian finite-dimensional laws by Kolmogorov extension
([existence of a pre-Brownian motion on path space](../ornstein-uhlenbeck-process/exists-is-pre-brownian-real-eval.md))
and then takes a continuous modification by Kolmogorov's lemma
([Brownian motion as a continuous modification of pre-Brownian motion](exists-is-brownian-real-modification.md)).

## Informally uses

- [Closure of real Gaussian laws under $L^2$ limits](../../distributions/continuous/closure-of-gaussian-laws-under-l-limits/of-tendsto-e-lp-norm-real.md):
  Lemme 14.2.2 of the ENS notes, which shows that the white-noise series defining $B_t$ is
  Gaussian.

## Background

- [Donsker's invariance principle](../../central-limit-theorems/donsker-s-invariance-principle/donsker-invariance-principle.md):
  its statement takes a Brownian motion as given; this theorem shows that one exists.

## Sources

- J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires*, lecture notes, École normale supérieure, Théorème 14.2.1 ("Le mouvement brownien existe") and Lemme 14.2.2.
- J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in Mathematics 274, Springer, 2016, Chapter 2.
