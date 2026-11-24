# Majorizing measure theorem

There is a universal constant $L > 0$ such that for every centred Gaussian process
$(X_t)_{t \in T}$ of measurable random variables on a probability space, indexed by a finite nonempty set, with canonical distance
$d(s, t) = (\mathbb{E}(X_s - X_t)^2)^{1/2}$,

$$\frac1L\,\gamma_2(T, d) \le \mathbb{E}\sup_{t \in T} X_t \le L\,\gamma_2(T, d)$$

(Fernique and Talagrand; Talagrand, *Upper and Lower Bounds for Stochastic Processes*, 2nd ed.,
2021, Theorem 2.10.1). The upper bound is the generic chaining bound; the lower bound says that
control of $\mathbb{E}\sup_t X_t$ forces the existence of a small admissible sequence. A process
is Gaussian when its law on $\mathbb{R}^T$ is a Gaussian measure. When the canonical distance is a metric, the
upper half is the generic chaining bound for Gaussian processes.

## Informally uses

- [Generic chaining bound for Gaussian processes, canonical form](integral-i-sup-le-gamma-two-canonical-di.md):
  the upper inequality is Theorem 2.7.11, with $\gamma_2$ for the canonical distance as in this statement and
  $L = 10$, when the canonical distance is a metric; with a pseudo-distance it applies after identifying indices
  at distance zero.
- [Sudakov minoration](sudakov-minoration.md): the first ingredient of Talagrand's proof of the
  lower bound (Lemma 2.10.2), with Gaussian concentration (Lemma 2.10.6) and the partitioning
  scheme of Theorem 2.9.1.
