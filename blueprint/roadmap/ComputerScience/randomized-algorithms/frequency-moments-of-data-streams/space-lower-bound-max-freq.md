# Linear space for approximating the largest multiplicity

For every fixed $0 < \varepsilon < 1/2$ there is $c > 0$ such that every randomized streaming
algorithm over $\{0, \dots, n - 1\}$ with $s$ bits of memory that, on every nonempty stream of length at
most $2n$, outputs $Y$ with $|Y - F^*_\infty| \ge F^*_\infty/3$ with probability less than
$\varepsilon$ uses $s \ge cn$ bits. The empty stream, which the source does not exclude, is excluded: there $F^*_\infty = 0$ and no
output meets the strict accuracy requirement; the source's proof only uses streams with
$F^*_\infty \in \{1, 2\}$.

The statement is in the [public-randomness model](streaming-algorithm.md), where the random seed is
not charged to the memory. That makes it at least as strong as the source's, and the source's
proof still applies:

- Alice and Bob share the seed as a public coin. Alice runs the algorithm on the elements of $x$
  and sends the $s$-bit memory content.
- Bob answers "disjoint" at once if $y = \emptyset$. Otherwise the stream ($x$ followed by $y$) is
  nonempty: he finishes the run and answers "intersect" iff the output is at least $4/3$.
- The intervals $(2/3, 4/3)$ and $(4/3, 8/3)$ are disjoint, so this public-coin protocol has cost
  $s + O(1)$ and error less than $\varepsilon$. Hence $s + O(1) = \Omega(n)$.
- For $n \ge 1$ one memory state cannot separate the streams $[0]$ and $[0, 0]$, so $s \ge 1$ and
  the additive constant is absorbed into $c$.

## Informally uses

- [Randomized communication complexity of disjointness](../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/rand-complexity-disj-fn-ge.md): the public-coin $\Omega(n)$ bound that the one-way protocol above must respect.

## Background

- [Largest multiplicity of a stream](max-freq.md): the quantity being approximated.
- [Randomized streaming algorithm with $s$ bits of memory](streaming-algorithm.md): the model, and why the free seed is harmless.

## Sources

- N. Alon, Y. Matias and M. Szegedy, "The space complexity of approximating the frequency moments", *J. Comput. System Sci.* 58 (1999) 137–147, Proposition 3.1 and its proof.
