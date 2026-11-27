# Chan-He: 3SUM reduces to polylogarithmically many Convolution-3SUM instances

There is a deterministic reduction that maps a list $x$ of $n \ge 1$ integers of absolute value at most $U \ge 1$ to a list of Convolution-3SUM instances such that $x$ has a solution at three pairwise distinct positions if and only if some instance has a solution. For an absolute constant $c$, the number of instances is at most $(\log_2(2nU))^{c}$, each instance has length at most $n\,(\log_2(2nU))^{c}$ and entries of absolute value at most $c\,U$, and the reduction runs in time $n^{3/2}(\log_2(2nU))^{c}$. Consequently, if Convolution-3SUM of length $N$ with entries of absolute value at most $N^{\kappa}$ can be solved in time $O(N^{2-\varepsilon})$ for some $\varepsilon > 0$ and every constant $\kappa$, then distinct-position 3SUM on $n$ integers of absolute value at most $n^{\kappa}$ can be solved in time $O(n^{2-\varepsilon'})$ for some $\varepsilon' > 0$ and every constant $\kappa$.

## Proof sketch

Cases (i) and (ii) of the three-set decomposition are decided by sorting; if one holds, output the one-entry instance $X = Y = Z = (0)$, which has a solution. Otherwise recurse from each of the $O(\log^2 n)$ three-set instances. Each node chooses a modulus $M = pq$ by the collision lemma, with primes up to $m = O(\sqrt{n}\,\log^2(2nU))$, searching first for $p$ and then for $q$ at cost $O(|Q|\, n \log n)$, emits the Convolution-3SUM instance of its light elements (length $2M \le 2m^2$), and branches into three children, each replacing one set by its heavy elements. A set of size $s$ keeps at most $s^2/(2n)$ heavy elements, so along any branch each set is empty after $O(\log\log n)$ shrinking steps; the recursion therefore has depth $O(\log\log n)$ and $(\log n)^{O(1)}$ nodes.

## Depends on

- [The 3SUM, APSP and Orthogonal Vectors hypotheses](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-3sum-apsp-and-orthogonal-vectors-hypotheses.md)
- [Convolution-3SUM](convolution-three-sum.md)
- [Fine-grained reductions](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/fine-grained-reductions.md)

## Proof depends on

- [Distinct-position 3SUM as finitely many three-set problems](three-sum-as-three-set-problems.md)
- [Choosing a hashing modulus with few heavy elements](chan-he-modulus-choice.md)
- [One node of the Chan-He recursion](chan-he-recursion-node.md)

## Sources

- T. M. Chan and Q. He, "Reducing 3SUM to Convolution-3SUM", Symposium on Simplicity in Algorithms (SOSA), 2020.
