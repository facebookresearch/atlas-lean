# Generic chaining and Gaussian processes

How large is $\mathbb{E}\sup_{t \in T} X_t$ for a centred process whose increments are
sub-Gaussian for a distance $d$ on $T$? Talagrand's generic chaining answers with the geometry of
$(T, d)$ alone. Approximate each $t$ by points $\pi_n(t)$ taken from sets of at most
$N_n = 2^{2^n}$ points, write $X_t - X_{t_0}$ as the telescoping sum of the increments
$X_{\pi_n(t)} - X_{\pi_{n-1}(t)}$, and control all increments at level $n$ at once by a union
bound over at most $N_{n+1}$ pairs. The outcome is
$\mathbb{E}\sup_t X_t \le L\,\gamma_2(T, d)$, where $\gamma_2$ is the infimum, over admissible
sequences of partitions, of $\sup_t \sum_{n \ge 0} 2^{n/2} \Delta(A_n(t))$. For Gaussian processes
with their canonical distance the bound is sharp: the majorizing measure theorem of Fernique and
Talagrand gives $\gamma_2(T, d)/L \le \mathbb{E}\sup_t X_t$, and its proof starts from Sudakov's
minoration.

The index set is finite throughout, as in the source: for an infinite $T$ the supremum is defined
through finite subsets. The generic chaining bound holds with the explicit constant
$L = 10$, and Dudley's entropy bound $\mathbb{E}\sup_t X_t \le 17\sum_n 2^{n/2} e_n(T)$, the
classical form in which the sets of the chain are optimal coverings, with $L = 17$. For a centred
Gaussian process whose canonical distance is the metric, the increments satisfy the sub-Gaussian
condition, which gives the upper half of the majorizing measure theorem; Talagrand's proof of its
lower half starts from Sudakov's minoration.

Source: M. Talagrand, *Upper and Lower Bounds for Stochastic Processes: Decomposition Theorems*,
2nd ed., Springer 2021, Chapter 2 (theorem numbers on these pages refer to this edition).

- [Admissible sequence of partitions](admissible-sequence.md)
- [The first partition is trivial](cell-zero.md)
- [Sub-Gaussian increment condition](satisfies-increment-condition.md)
- [Cardinality bounds of generic chaining](chaining-card.md)
- [Diameter for a distance function](diam-with.md)
- [The diameter for the extended distance is the usual diameter](diam-with-edist.md)
- [The diameter is at most $\gamma_\alpha$](diam-with-univ-le-gamma-functional.md)
- [Talagrand's $\gamma_\alpha$ functional](gamma-functional.md)
- [$\gamma_\alpha$ is finite on a finite space](gamma-functional-lt-top.md)
- [Generic chaining bound](integral-i-sup-le-gamma-two.md)
- [Generic chaining bound, real form](integral-i-sup-le-gamma-two-to-real.md)
- [The chaining argument along a finite chain](lintegral-i-sup-sub-le-of-chain.md)
- [The chaining bound for a centred process](of-real-integral-i-sup-le-of-chain.md)
- [Entropy numbers](entropy-number.md)
- [Entropy numbers from finite covers](entropy-number-le-of-is-cover.md)
- [Dudley's entropy bound](integral-i-sup-le-dudley.md)
- [Dudley's sum is finite on a finite space](tsum-entropy-number-lt-top.md)
- [Entropy numbers are controlled by $\gamma_2$](two-rpow-mul-entropy-number-le-gamma-two.md)
- [Two-sided Gaussian tail](gaussian-real-abs-tail.md)
- [Increments of a centred Gaussian process](measure-real-abs-sub-ge-le-of-is-gaussia.md)
- [Generic chaining bound for Gaussian processes](integral-i-sup-le-gamma-two-of-is-gaussi.md)
- [The metric is the canonical distance](edist-eq-canonical-dist.md)
- [Generic chaining bound for Gaussian processes, canonical form](integral-i-sup-le-gamma-two-canonical-di.md)
- [Canonical distance of a process](canonical-dist.md)
- [Majorizing measure theorem](majorizing-measure.md)
- [Sudakov minoration](sudakov-minoration.md)

## Related topics

- [Uniform laws and Rademacher complexity](../uniform-laws-and-rademacher-complexity/README.md):
  the expected supremum of an empirical process is the quantity that chaining bounds when the
  process is conditionally sub-Gaussian (Rademacher averages).
- [Suprema of selector and empirical processes](../suprema-of-selector-and-empirical-processes/README.md):
  Park and Pham's theorems settled Talagrand's conjectures on selector processes, the
  non-Gaussian counterpart of the majorizing measure theorem.
- [Transport-cost inequalities](../../concentration-inequalities/transport-cost-inequalities/README.md):
  Gaussian concentration, which the proof of the majorizing measure theorem uses for the
  supremum of a Gaussian process (Talagrand, Lemma 2.10.6), follows from Talagrand's quadratic
  transport inequality for the Gaussian measure.
