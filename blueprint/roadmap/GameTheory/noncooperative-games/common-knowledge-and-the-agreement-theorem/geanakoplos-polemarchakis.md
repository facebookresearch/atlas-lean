# We can't disagree forever

Finitely many agents share a prior, a finite measure on a finite set $\Omega$ of states in which every
singleton is measurable. In each round every agent
announces publicly its current posterior of the event $A$, and every agent refines its information
partition by the level sets of the announced profile of posteriors. Then the partitions stop
changing after finitely many rounds $T$, and at round $T$ all agents' posteriors of $A$ are equal
at every state whose meet cell is not null.

The proof: partitions only get finer, and a finite set has finitely many partitions, so the
sequence stabilises. At a fixed point every agent's posterior is constant on every agent's cells,
hence on the cells of the meet; the posteriors are then common knowledge and the
[agreement theorem](agreement.md) applies.

Compared with the source: Geanakoplos and Polemarchakis assume finite information partitions,
whereas here the state space is finite; in their paper the two agents communicate back and
forth, and the abstract also states that any number of rounds can be needed and that the limit
need not be the posterior given the pooled information; here any finite family announces
simultaneously, and no bound on $T$ is claimed.

## Informally uses

- [At a fixed point of the dialogue, posteriors agree](posterior-eq-of-dialogue-step-eq.md): the
  conclusion at round $T$.
- [Partitions only get finer during a dialogue](dialogue-antitone.md): the stabilisation.

## Sources

- J. D. Geanakoplos and H. M. Polemarchakis, "We can't disagree forever", J. Econom. Theory 28(1) (1982), 192–200 (abstract consulted, not the full text: secondary for the details of the protocol).
