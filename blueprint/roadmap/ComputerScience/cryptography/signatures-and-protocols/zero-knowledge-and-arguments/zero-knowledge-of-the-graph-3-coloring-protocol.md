# Zero knowledge of the graph 3-coloring protocol

For the graph 3-coloring protocol with a perfectly binding, computationally hiding commitment scheme, run $n|E|$ times on a graph $G = (V, E)$ with $|V| = n$ and $|E| \ge 1$:

**Proposition.** The protocol is a zero-knowledge proof for the language of 3-colorable graphs.

For one round, the simulator for a verifier $V^*$ with auxiliary input $z$ picks a random edge $(i_0, j_0) \in E$ and random distinct colors for $i_0$ and $j_0$, colors
every other vertex $1$, commits to these colors as the honest prover does and feeds the commitments to $V^*(x, z)$ with truly random coins. If $V^*$ aborts or sends a challenge that is not an edge,
the simulator outputs the view of $V^*$ so far, as the honest prover would end the round; if $V^*$ asks for $(i_0, j_0)$, it opens the two commitments and outputs the view of $V^*$;
and only if $V^*$ asks for a different edge of $E$ does it rewind and restart, at most $n|E|$ times, outputting fail if no attempt succeeded.
Hiding makes the commitments to the improper coloring indistinguishable from honest ones, so $V^*$ asks for the guessed edge with probability close to $1/|E|$
and the output is computationally indistinguishable from the real view. Zero knowledge of the repeated protocol follows from zero knowledge of one round by
sequential composition.

## Depends on

- [Zero-knowledge interactive proofs](zero-knowledge-interactive-proofs.md)
- [Soundness of the graph 3-coloring protocol](soundness-of-the-graph-3-coloring-protocol.md)

## Proof depends on

- [The hybrid step](../../security-games/games-and-advantages/advantage-hybrid-uniform.md)

## Sources

- R. Pass and A. shelat, *A Course in Cryptography*, lecture notes, Cornell University, 2010, <https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf>: Protocol 127.5, Proposition 127.6 with its proof and Simulator 128.7, and Theorem 175.1 (sequential composition).
