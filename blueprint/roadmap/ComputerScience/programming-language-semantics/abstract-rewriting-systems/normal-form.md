# Reachable normal form

Let $\to$ be a binary relation on a type $\alpha$, an abstract reduction system oriented from a state to its reduct, and write $\to^*$ for its reflexive–transitive closure. A state $n$ is *normal* if there is no $y$ with $n \to y$; in particular a state with a loop $n \to n$ is not normal.

For states $a, n \in \alpha$, $n$ is a **reachable normal form** of $a$ if

$$a \to^* n \quad\text{and}\quad n \text{ is normal}.$$

The predicate fixes a particular normal form; it does not assert that it is the only one.

## Sources

- Terese, *Term Rewriting Systems*, Cambridge Tracts in Theoretical Computer Science 55, Cambridge University Press, 2003, Chapter 1 (abstract reduction systems). ISBN 978-0-521-39115-3.
