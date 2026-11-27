# The blocking lemma for deferred acceptance

Let $\mu_0$ be the proposer-optimal stable matching (the outcome of proposer-proposing deferred acceptance) and $\mu$ any matching. If the set $Q$ of proposers who strictly prefer $\mu$ to $\mu_0$ is nonempty, then $\mu$ is blocked by a pair $(x, \mu(q))$ with $q \in Q$ and $x \notin Q$. The same holds for strict, possibly incomplete preference lists with unequal sides, provided $\mu$ is individually rational (no agent is matched to a partner it finds unacceptable). Consequently no coalition of proposers can all strictly gain by misreporting under deferred acceptance (weak group strategy-proofness for proposers; the strong form fails, since one proposer can misreport to help another without losing anything itself).

## Proof sketch

Either some proposer of $Q$ is matched in $\mu$ to the $\mu_0$-partner of a proposer outside $Q$, or the receivers $\mu(Q)$ coincide with $\mu_0(Q)$; in the latter case consider the last proposal in deferred acceptance made to a receiver in $\mu(Q)$.

## Depends on

- [Stable matching](../stable-marriage-problem/is-stable-matching.md)
- [Blocking pair](../stable-marriage-problem/is-blocking-pair.md)

## Proof depends on

- [Gale–Shapley theorem](../stable-marriage-problem/gale-shapley-exists-stable-matching.md)

## Sources

- D. Gale and M. Sotomayor, "Some Remarks on the Stable Matching Problem", Discrete Applied Mathematics 11(3), 1985.
- D. Gusfield and R. W. Irving, "The Stable Marriage Problem: Structure and Algorithms", MIT Press, 1989.
