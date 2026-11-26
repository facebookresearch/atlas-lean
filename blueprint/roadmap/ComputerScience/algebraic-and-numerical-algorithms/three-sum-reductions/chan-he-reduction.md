# Chan-He: 3SUM reduces to polylogarithmically many Convolution-3SUM instances

There is a deterministic reduction that maps a 3SUM input $x$ of $n \ge 1$ integers of absolute value at most $U$ to a list of Convolution-3SUM instances such that $x$ has a solution at three distinct positions if and only if some instance has a solution. Each instance has length $O(m^2)$ where $m = \tilde O(\sqrt{n})$ is the prime-search range, entries of absolute value polynomial in $n$ and $U$, and the number of instances is at most $\big(2 b(2U)^2 + 2\big)\big(2\lfloor \log_2 n \rfloor + 2\big)^5$, where $b(\cdot)$ is the bit length. The reduction runs in time $O(n \cdot \mathrm{polylog}(n U))$. Consequently, for polynomially bounded inputs, a truly subquadratic Convolution-3SUM algorithm yields a truly subquadratic 3SUM algorithm.

## Proof sketch

Recurse from the three-set decomposition. Each node hashes by the modulus from the collision lemma, solves its light part with one Convolution-3SUM instance, and branches into three children with heavy sets of size at most $|S|^2/(2n)$, so sizes fall doubly exponentially and the recursion has depth $O(\log\log n)$ and polylogarithmically many nodes.

## Depends on

- [Distinct-position 3SUM](distinct-position-three-sum.md)
- [Convolution-3SUM](convolution-three-sum.md)
- [Fine-grained reductions](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/fine-grained-reductions.md)

## Proof depends on

- [Distinct-position 3SUM as finitely many three-set problems](three-sum-as-three-set-problems.md)
- [Choosing a hashing modulus with few heavy elements](chan-he-modulus-choice.md)
- [One node of the Chan-He recursion](chan-he-recursion-node.md)

## Sources

- T. M. Chan and Q. He, "Reducing 3SUM to Convolution-3SUM", Symposium on Simplicity in Algorithms (SOSA), 2020.
