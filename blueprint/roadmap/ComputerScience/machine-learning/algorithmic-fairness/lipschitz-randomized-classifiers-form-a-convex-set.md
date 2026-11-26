# Lipschitz randomized classifiers form a convex set

Let $V$ be a set, $A$ a finite set and $d : V \times V \to \mathbb{R}$ any function. The maps $M : V \to \Delta(A)$ with
$\mathrm{TV}(M(x), M(y)) \le d(x, y)$ for all $x, y \in V$ form a convex subset of $\Delta(A)^V$: if $M$ and $M'$ are two
of them and $0 \le a \le 1$, the mixture $x \mapsto a M(x) + (1 - a) M'(x)$ is one too. Here $\Delta(A)$ is the set of
probability vectors on $A$ (nonnegative entries summing to $1$) and
$\mathrm{TV}(p, q) = \frac12 \sum_{a \in A} \lvert p_a - q_a \rvert$.

## Proof

A mixture of probability vectors is a probability vector, and $\mathrm{TV}(p, q)$ is a seminorm of $p - q$, hence convex,
so the distance between the mixtures at $x$ and $y$ is at most
$a \, \mathrm{TV}(M(x), M(y)) + (1 - a) \, \mathrm{TV}(M'(x), M'(y)) \le d(x, y)$.

## Related topics

- [Individual fairness: maximal bias and the linear-programming formulation](remaining-clauses-of-individual-fairness-as-a-lipschitz-cond.md),
  which collects the linear-programming formulation over this set.

## Sources

- C. Dwork, M. Hardt, T. Pitassi, O. Reingold and R. Zemel, *Fairness through awareness*, ITCS 2012; arXiv:1104.3913, Definition 2.1 (Lipschitz mapping) and Figure 1 (the fairness linear program, whose feasible set this is). <https://arxiv.org/abs/1104.3913>
