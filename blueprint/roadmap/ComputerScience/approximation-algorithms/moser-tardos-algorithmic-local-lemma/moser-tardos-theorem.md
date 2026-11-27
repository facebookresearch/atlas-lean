# Moser-Tardos theorem: the resampling algorithm finds an assignment avoiding all events

In the variable model, suppose there are $x_i \in [0,1)$ such that for every event

$$
\Pr[A_i] \le x_i \prod_{j \in \Gamma(i)} (1 - x_j),
$$

where $\Gamma(i)$ contains every other event sharing a variable with $A_i$. Then for every valid selection rule the expected number of resamplings of $A_i$ is at most $x_i/(1-x_i)$, so the expected total number of resampling steps is at most $\sum_i x_i/(1-x_i)$. Almost surely the algorithm stops after finitely many steps, and a rule that stops only when no event holds reaches an assignment avoiding every $A_i$; in particular such an assignment exists.

## Proof sketch

The $k$-th resampling of $A_i$ yields a distinct proper witness tree rooted at $i$, so the expected number of resamplings of $A_i$ is at most the sum over proper structures rooted at $i$ of their occurrence probabilities. The witness tree lemma bounds this by $x_i/(1-x_i)$, uniformly over all valid rules. Finite expectation implies almost-sure termination.

## Depends on

- [Moser-Tardos resampling algorithm in the variable model](moser-tardos-algorithm.md)
- [Lovász local lemma, general form](../../../Combinatorics/probabilistic-combinatorics/lovasz-local-lemma-general-finite.md)

## Proof depends on

- [Moser-Tardos witness tree lemma](moser-tardos-witness-tree-lemma.md)

## Sources

- Robin A. Moser and Gábor Tardos, "A Constructive Proof of the General Lovász Local Lemma", Journal of the ACM 57(2), 2010.
