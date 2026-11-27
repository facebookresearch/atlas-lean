# Posterior probability

Let $\mu$ be a measure on a set $\Omega$ of states (in this topic a finite measure on a finite set, the
common prior) and $\mathcal P$ an agent's information partition. The agent's posterior probability of the
event $A$ at the state $\omega$ is

$$q(\omega) = \frac{\mu(A \cap P(\omega))}{\mu(P(\omega))},$$

the masses being taken as real numbers (an infinite mass counts as $0$), with the convention $x / 0 = 0$.
It is the conditional probability of $A$ given the cell $P(\omega)$; on a null cell the posterior is $0$,
whereas Aumann assumes the relevant cells nonnull.

## Related topics

- [Posteriors are conditional probabilities](posterior-eq-cond.md): the identification with the
  conditional probability measure.

## Sources

- R. J. Aumann, "Agreeing to disagree", Ann. Statist. 4(6) (1976), 1236–1239, p. 1237 ("$q_i(\omega) = p(A \cap P_i(\omega))/p(P_i(\omega))$").
