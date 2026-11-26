# Normalizer of an abstract reduction system

Let $\to$ be a binary relation on a type $\alpha$, an abstract reduction system oriented from a state to its reduct, and write $\to^*$ for its reflexive–transitive closure. A state $n$ is *normal* if there is no $y$ with $n \to y$.

A **normalizer** for $\to$ consists of

- a function $N : \alpha \to \alpha$ (the chosen result),
- for every $a \in \alpha$, a proof that $a \to^* N(a)$, and
- for every $a \in \alpha$, a proof that $N(a)$ is normal.

It chooses one reachable normal form of each state; without further hypotheses different normalizers may choose differently.

## Sources

- Terese, *Term Rewriting Systems*, Cambridge Tracts in Theoretical Computer Science 55, Cambridge University Press, 2003, Chapter 1 (abstract reduction systems). ISBN 978-0-521-39115-3.
