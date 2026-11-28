# Individual fairness: maximal bias and the linear-programming formulation

For a finite set $V$ of individuals with a metric $d$, a randomized classifier $M : V \to \Delta(A)$ is Lipschitz when the total variation
distance between $M(x)$ and $M(y)$ is at most $d(x, y)$, and the bias between distributions $S$ and $T$ on $V$ is the largest statistical-parity
difference $\mu_S(0) - \mu_T(0)$ over Lipschitz classifiers with outcomes $\{0, 1\}$ (Dwork et al., Definition 3.2). The upper bound of this bias
by the earthmover distance, inequality (9) of Dwork et al., Theorem 3.3, is the clause not collected here. This node collects the remaining
clauses of Dwork et al.

## Expansion

A sound expansion has separate pages for:

1. **Maximal bias equals earthmover distance:** if furthermore $d(x, y) \le 1$ for all $x, y$, the bias is at least, hence equal to, the $d$-earthmover
   distance between $S$ and $T$ (Dwork et al., Theorem 3.3, inequality (10)).
2. **Linear-programming formulation:** for finitely many individuals and outcomes and a loss that is linear in the outcome probabilities,
   computing a loss-minimizing classifier subject to the Lipschitz condition, with total variation distance or with the relative
   $\ell_\infty$ distance $D_\infty$ of the source, is a linear program of size polynomial in the numbers of individuals and outcomes (Dwork et al.,
   Lemmas 2.1 and 2.2).

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Lipschitz randomized classifiers, statistical-parity bias and the earthmover distance (Dwork et al., Sections 2–3).

## Sources

- Fairness Through Awareness — Dwork, Hardt, Pitassi, Reingold, Zemel, ITCS 2012, Lemmas 2.1–2.2, Definitions 3.2–3.3 and Theorem 3.3. <https://www.cs.toronto.edu/~zemel/documents/fairAwareItcs2012.pdf>
