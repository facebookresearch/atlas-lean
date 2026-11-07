# There is a unique infinite comma-child path from 1 in base 3

There is exactly one
sequence $a_0, a_1, \dots$ of natural numbers with $a_0 = 1$ such that for every $i$ there is a
comma candidate digit $y$ of $a_i$ in base $3$ with $a_{i+1} = a_i + 3\,(a_i \bmod 3) + y$,
that is, each $a_{i+1}$ is a base-3 comma-child of $a_i$.

The paper also describes this path (at branch points it alternately takes the lower and the
higher child); that description is not part of this statement.

## Sources

- Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci Quarterly 62 (2024), no. 3, Theorem 10.1 (`fq-2024-sloane05302024-thm-10.1`).
