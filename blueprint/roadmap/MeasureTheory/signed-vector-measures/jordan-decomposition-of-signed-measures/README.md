# Jordan decomposition of a finite signed measure

Let $s$ be a finite signed measure on a measurable space $X$. Then $s = s^+ - s^-$ for two finite
positive measures $s^+$ and $s^-$ that are mutually singular, built from a Hahn decomposition of $s$. The card's
second statement shows that this pair, the Jordan decomposition of $s$, is the only pair of mutually singular finite
measures whose difference is $s$.

## Idea

With a Hahn decomposition $X = P \cup N$, set $s^+(E) = s(E \cap P)$ and $s^-(E) = -s(E \cap N)$. Both
are finite positive measures, $N$ is null for $s^+$ and $P$ is null for $s^-$. For uniqueness, if $s = \mu - \nu$
with $\mu \perp \nu$, the sets on which $\mu$ and $\nu$ live form another Hahn decomposition, and two Hahn
decompositions differ by sets that are null for $s$. The total variation $|s| = s^+ + s^-$ measures the size of $s$,
and $s^+(E) = \sup\{s(F) : F \subseteq E \text{ measurable}\}$.

## Statements

- [Jordan decomposition of a finite signed measure](to-signed-measure-to-jordan-decomposition.md)
- [Uniqueness of the Jordan decomposition](to-signed-measure-injective.md): two pairs of mutually singular finite measures with the same difference are equal.

## Background

- [Hahn decomposition of a finite signed measure](../hahn-decomposition-of-signed-measures/hahn-decomposition-theorem/README.md): used in the construction
- [Mutually singular measures](../absolute-continuity-and-decomposition-of-vector/mutually-singular-measures/README.md): singularity

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, result 9.30 (version read: the open-access PDF dated 12 June 2026).
