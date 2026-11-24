# Well-based sets

A finite set $Q$ of positive integers is well based (Kitaev;
Valyuzhenich) if for every $x \in Q$ and every natural number $a$ with $0 < a < x$, at least one
of $a$ and $x - a$ lies in $Q$.

The empty set is well based, as in Allen's equivalent formulation. If $Q$ is nonempty, its least
element is $1$: otherwise the split of its least element $x$ into $1$ and $x - 1$ would have
neither part in $Q$.

In Lean, `IsWellBased Q` is the split condition alone on a finite set of natural numbers. For
example, $\{0\}$ satisfies it vacuously. Allen's notion is `IsPositiveWellBased Q`, which also
requires $0 \notin Q$.

## Sources

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer Sequences 28 (2025), Article 25.3.7, Section 5.1.
