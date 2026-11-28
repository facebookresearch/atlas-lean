# Near-optimality dimension

Let $\ell$ be a [semi-metric](semi-metric.md) on a set $\mathcal X$ and let $f \colon \mathcal X \to \mathbb{R}$ attain
its maximum $f^* = \max_{\mathcal X} f$. For $\varepsilon > 0$, the set of $\varepsilon$-optimal points is

$$
\mathcal X_\varepsilon = \{x \in \mathcal X : f(x) \ge f^* - \varepsilon\}.
$$

Let $\eta > 0$ and $\varepsilon_0 > 0$. Real numbers $d \ge 0$ and $C > 0$ satisfy the *$\eta$-near-optimality
condition up to $\varepsilon_0$* for $f$ if, for every $\varepsilon$ with $0 < \varepsilon \le \varepsilon_0$, every
finite set $S \subseteq \mathcal X_\varepsilon$ whose balls $B_\ell(x, \eta \varepsilon)$, $x \in S$, are pairwise
disjoint has at most $C \varepsilon^{-d}$ elements:

$$
|S| \le C \varepsilon^{-d},
$$

where $\varepsilon^{-d}$ is a real power. The *$\eta$-near-optimality dimension* of $f$ is the smallest $d \ge 0$ for
which some $\varepsilon_0 > 0$ and $C > 0$ satisfy the condition, when there is a smallest one, and such a $C$ is a
corresponding constant. It depends on $f$, on $\ell$ and on $\eta$, but not on any partition of $\mathcal X$.

The sources require the bound for every $\varepsilon > 0$, which holds only for $d = 0$, since a maximizer $x^*$ of
$f$ lies in every $\mathcal X_\varepsilon$ and $S = \{x^*\}$ gives $1 \le C \varepsilon^{-d}$; the condition here is
the local one of the monograph's Remark 3.3, which the monograph uses with its loss bounds in Section 3.3.2,
Example 2, and the proofs use it only at $\varepsilon = \delta(h) \le \delta(0)$. The sources also ask that the
largest number of such disjoint balls be less than $C \varepsilon^{-d}$; their use of the definition needs only "at
most", which is taken here. The loss bounds of [DOO](deterministic/loss-of-doo.md) and
[SOO](deterministic/loss-of-soo.md) use the condition with $\eta = \nu$, the constant of
[well-shaped cells](well-shaped-cells.md), and $\varepsilon_0 = \delta(0)$, and hold for every pair $(d, C)$ that
satisfies it; they do not need a smallest $d$ to exist.

## Sources

- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Definition 1 (with $\eta = \nu$).
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.3.1, Definition 3.1 and Remark 3.3, and Section 3.3.2,
  Example 2, which uses the local near-optimality dimension of Remark 3.3 with the loss bounds.

## Depends on

- [Semi-metric](semi-metric.md)
- [Cardinality of a finite set](../../../../../SetTheory/finite-sets/cardinality-of-finite-sets/card.md)
- [Real power of a real number](../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow.md)
