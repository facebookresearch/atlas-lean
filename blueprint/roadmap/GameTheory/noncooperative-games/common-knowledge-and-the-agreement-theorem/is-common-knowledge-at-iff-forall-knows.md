# Common knowledge as iterated knowledge

An event $E$ is common knowledge at $\omega$ (it contains the meet cell of $\omega$) if and only
if, for every finite sequence of agents $i_1, \dots, i_k$ (repetitions allowed, $k \ge 0$),

$$\omega \in K_{i_1} K_{i_2} \cdots K_{i_k}(E),$$

that is, at $\omega$ agent $i_1$ knows that agent $i_2$ knows that … agent $i_k$ knows $E$.

The proof follows Aumann's argument: a state lies in the meet cell of $\omega$ exactly when it is
reachable from $\omega$ by a finite chain of states in which consecutive states share a cell of
some agent's partition, and that chain gives the sequence of agents.

Compared with the source: Aumann argues the equivalence informally for two agents, with chains
that alternate between the two partitions; here the family of agents is arbitrary.

## Background

- [Common knowledge](is-common-knowledge-at.md): the definition through the meet.
- [Iterated knowledge along a chain of agents](knows-chain.md): the event
  $K_{i_1} \cdots K_{i_k}(E)$.

## Sources

- R. J. Aumann, "Agreeing to disagree", Ann. Statist. 4(6) (1976), 1236–1239, p. 1237 (the paragraph beginning "To see that the formal definition of 'common knowledge' is equivalent to the informal description").
