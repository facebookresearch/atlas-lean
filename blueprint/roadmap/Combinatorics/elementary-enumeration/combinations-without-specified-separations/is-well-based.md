# Well-based sets

A finite set $Q$ of natural numbers satisfies the split condition if for every $x \in Q$ and
every natural number $a$ with $0 < a < x$, at least one of $a$ and $x - a$ lies in $Q$.
The Lean predicate `IsWellBased Q` states this condition alone: for example, $\{0\}$ satisfies
it vacuously.

For a nonempty set of positive integers, the split condition is equivalent to the well-based
sequence condition of Kitaev and Valyuzhenich for its increasing enumeration. Such a set has
least element $1$ if it satisfies the split condition: otherwise neither part of the split
$x = 1 + (x - 1)$ of its least element $x$ could lie in $Q$.

Allen's formulation also counts the empty set as well based. Lean's `IsPositiveWellBased Q`
encodes Allen's convention by requiring $0 \notin Q$ and the split condition, but not
nonemptiness.

## Sources

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer Sequences 28 (2025), Article 25.3.7, Section 5.1.
