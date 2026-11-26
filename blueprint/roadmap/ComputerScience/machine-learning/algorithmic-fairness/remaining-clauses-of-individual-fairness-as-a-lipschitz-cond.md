# Individual fairness: maximal bias and the linear-programming formulation

For a finite set $V$ of individuals with a metric $d$, a randomized classifier $M : V \to \Delta(A)$ is Lipschitz when the total variation
distance between $M(x)$ and $M(y)$ is at most $d(x, y)$, and the bias between distributions $S$ and $T$ on $V$ is the largest statistical-parity
difference $\mu_S(0) - \mu_T(0)$ over Lipschitz classifiers with outcomes $\{0, 1\}$ (Dwork et al., Definition 3.2). The Lipschitz condition,
the earthmover distance, and the bound for one fixed classifier that is Lipschitz for $d$, whose outcome distributions on $S$ and $T$ are at
most the $d$-earthmover distance between $S$ and $T$ apart in total variation distance, are stated on separate pages, listed under the
dependencies. This node collects the clauses of Dwork et al. about the bias itself and the two linear-programming formulations.

## Expansion

A sound expansion has separate pages for:

1. **Maximal bias is at most the earthmover distance:** the bias between $S$ and $T$ is at most the $d$-earthmover distance between them
   (Dwork et al., Theorem 3.3, inequality (9)). Its proof applies the fixed-classifier bound to each classifier in the maximum, since
   $\mu_S(0) - \mu_T(0)$ is at most the total variation distance between the two outcome distributions.
2. **Maximal bias equals earthmover distance:** if furthermore $d(x, y) \le 1$ for all $x, y$, the bias is at least, hence equal to, the $d$-earthmover
   distance between $S$ and $T$ (Dwork et al., Theorem 3.3, inequality (10)).
3. **Linear program for total variation distance:** for finitely many individuals and outcomes and a loss that is linear in the outcome
   probabilities, computing a loss-minimizing classifier subject to the Lipschitz condition with total variation distance is a linear program
   of size polynomial in the numbers of individuals and outcomes (Dwork et al., Lemma 2.1).
4. **Linear program for the relative $\ell_\infty$ distance:** the same holds for the Lipschitz condition $D_\infty(M(x), M(y)) \le d(x, y)$, where
   $D_\infty(P, Q) = \sup_{a \in A} \log \max\{P(a)/Q(a), Q(a)/P(a)\}$ is the relative $\ell_\infty$ distance (Dwork et al., equation (6) and
   Lemma 2.2); each such constraint is a family of linear inequalities $M(x)(a) \le e^{d(x, y)} M(y)(a)$.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite of items 1 and 2: the statistical-parity bias, the maximum above (Dwork et al., Definition 3.2).
- Statement prerequisites of item 4: the relative $\ell_\infty$ distance $D_\infty$ (Dwork et al., equation (6)) and the $(D_\infty, d)$-Lipschitz
  condition (Dwork et al., Definition 2.1 with $D = D_\infty$). The Lipschitz condition linked under the dependencies uses total variation
  distance, so it covers items 1 to 3 only.

## Depends on

- [Individual fairness as a Lipschitz condition](is-lipschitz-fair.md)
- [Earthmover value](../../../Probability/not-yet-classified/part-17/finite-transport/earthmover.md)

## Proof depends on

- [Classifier-level earthmover bound](tv-dist-vec-mul-le-earthmover.md)

## Sources

- Fairness Through Awareness — Dwork, Hardt, Pitassi, Reingold, Zemel, ITCS 2012, Definition 2.1, equation (6), Lemmas 2.1–2.2, Definitions 3.2–3.3 and Theorem 3.3. <https://www.cs.toronto.edu/~zemel/documents/fairAwareItcs2012.pdf>
