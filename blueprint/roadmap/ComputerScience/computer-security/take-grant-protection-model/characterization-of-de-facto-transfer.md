# Characterization of de facto transfer

**Theorem.** Let $p$ and $q$ be vertices of a [protection graph](take-grant-protection-graphs.md) $G$. Then $\mathrm{can{\cdot}know{\cdot}f}(p, q, G)$ holds if and only if
there is an edge from $p$ to $q$ labelled $r$ or there is an [admissible rw-path](de-facto-rules-and-admissible-rw-paths.md) between $p$ and $q$.

The proof that an admissible rw-path suffices is by induction on its length: each of the four rw-paths of length two is handled by one of the de facto rules,
and a longer admissible path extends a shorter one by a read edge from a subject or a write edge into a subject.

## Depends on

- [De facto rules and admissible rw-paths](de-facto-rules-and-admissible-rw-paths.md)

## Sources

- M. Bishop and L. Snyder, *The Transfer of Information and Authority in a Protection System*, Research Report 166, Department of Computer Science, Yale University, July 1979, <http://nob.cs.ucdavis.edu/~bishop/notes/1979-yalecs-166/yale-166.pdf>: Theorem 3.1 and its proof (pp. 13–15).
