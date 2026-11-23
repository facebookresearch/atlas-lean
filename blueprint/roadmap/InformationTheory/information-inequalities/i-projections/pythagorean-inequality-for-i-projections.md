# I-projection: support and Pythagorean inequality

Let $Q > 0$ on a finite alphabet, let $\Gamma$ be a convex set of distributions (nonnegative
functions summing to $1$), and let $P^* \in \Gamma$ minimise $D(\cdot \| Q)$ over $\Gamma$. Then for every
$P \in \Gamma$:

1. $P(a) = 0$ wherever $P^*(a) = 0$ (the support of $P^*$ is the support of $\Gamma$);
2. $D(P\|P^*) + D(P^*\|Q) \le D(P\|Q)$, with $D(R\|S) = \sum_a R(a)\log(R(a)/S(a))$, natural log.

Item 1 makes $D(P\|P^*)$ in item 2 a genuine (finite) divergence: every term with $P^*(a) = 0$ has
$P(a) = 0$. This is the tutorial's Theorem 3.1 exactly (finite alphabet, $Q > 0$). Csiszár (1975)
proves it on arbitrary measurable spaces, and also proves the converse: a $P^* \in \Gamma$ satisfying
the inequality for all $P \in \Gamma$ is the I-projection.

The proof is the tutorial's: the [first-order condition](first-order-condition-for-i-projections.md)
gives item 1 and $\sum_a (P(a) - P^*(a))(\log P^*(a) - \log Q(a)) \ge 0$, and
[the divergence defect](divergence-defect-as-a-first-order-term.md) identifies that sum with
$D(P\|Q) - D(P\|P^*) - D(P^*\|Q)$.

## Background

- [Gibbs' inequality](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy-le-cross-entropy.md):
  $D(P\|P^*) \ge 0$, which makes the Pythagorean inequality imply that $P^*$ is the unique minimiser
  (a consequence not included in the statement).

## Sources

- I. Csiszár and P. C. Shields, *Information Theory and Statistics: A Tutorial*, Foundations and Trends in Communications and Information Theory 1(4) (2004), 417–528, Theorem 3.1.
- I. Csiszár, "I-divergence geometry of probability distributions and minimization problems", *Ann. Probab.* 3(1) (1975), 146–158, Theorem 2.2.
