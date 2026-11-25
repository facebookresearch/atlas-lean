# Lipschitz randomized classifiers form a convex set

Let $V$ and $A$ be finite sets and $d$ a metric on $V$. The maps $M : V \to \Delta(A)$ with $\mathrm{TV}(M(x), M(y)) \le d(x, y)$ for all $x, y \in V$ form a
convex subset of $\Delta(A)^V$, cut out by finitely many linear inequalities in the coordinates $M(x)_a$; minimizing an expected loss that is linear in $M$
over this set is a linear program.

## Proof

$\mathrm{TV}(p, q) = \frac12 \sum_a \lvert p_a - q_a \rvert$ is a norm of $p - q$, hence convex, so the constraint is preserved under convex combinations of maps.
Writing $\lvert M(x)_a - M(y)_a \rvert \le t_{xya}$ with auxiliary variables turns each constraint into linear inequalities.

## Related topics

- [Individual fairness: maximal bias and the linear-programming formulation](remaining-clauses-of-individual-fairness-as-a-lipschitz-cond.md)

## Sources

- C. Dwork, M. Hardt, T. Pitassi, O. Reingold and R. Zemel, *Fairness through awareness*, ITCS 2012; arXiv:1104.3913, Definition 2.1 (Lipschitz mapping), Figure 1 (the fairness LP) and Lemma 2.1 (with total variation distance it is a linear program of size polynomial in $\lvert V \rvert$ and $\lvert A \rvert$). <https://arxiv.org/abs/1104.3913>
