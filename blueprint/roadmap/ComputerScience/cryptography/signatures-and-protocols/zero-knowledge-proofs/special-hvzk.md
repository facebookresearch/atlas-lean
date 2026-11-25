# Perfect special honest-verifier zero knowledge

A [Sigma protocol](sigma-protocol.md) is perfectly special honest-verifier zero knowledge with a
per-challenge simulator, which receives the statement and a challenge $e$, if for every
statement–witness pair in the relation and every challenge $e$ the
[honest pair for the challenge $e$](challenge-transcript.md) has the simulator's distribution for $e$.
This is stronger than [perfect honest-verifier zero knowledge](hvzk.md), which only constrains a
uniform challenge.

## Sources

- I. Damgård, *On Σ-protocols*, lecture notes, Aarhus University, 2010.
