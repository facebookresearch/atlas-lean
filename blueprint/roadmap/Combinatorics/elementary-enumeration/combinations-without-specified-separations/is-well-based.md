# Well-based sets

A finite set $Q$ of natural numbers satisfies the split condition if for every $x \in Q$ and
every natural number $a$ with $0 < a < x$, at least one of $a$ and $x - a$ lies in $Q$.
The Lean predicate `IsWellBased Q` states this condition alone: for example, $\{0\}$ satisfies
it vacuously.

For sets of positive integers, this is the well-based condition of Kitaev and Valyuzhenich.
Lean's `IsPositiveWellBased Q` adds $0 \notin Q$, as in Allen's formulation. The empty set
satisfies both conditions. A nonempty set satisfying the positive version has least element
$1$: otherwise neither part of the split $x = 1 + (x - 1)$ of its least element $x$ could lie
in $Q$.

## Sources

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer Sequences 28 (2025), Article 25.3.7, Section 5.1.
