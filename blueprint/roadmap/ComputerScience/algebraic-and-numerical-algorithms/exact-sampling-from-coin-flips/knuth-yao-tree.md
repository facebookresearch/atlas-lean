# Knuth-Yao sampling tree of a finite distribution

Let $p$ be a probability distribution on a finite set $\alpha$. The *Knuth-Yao tree* of $p$ is the DDG tree over $\alpha$ (reading fair bits) that places a leaf labelled $a$ at depth $k \ge 0$ exactly when $\lfloor 2^k p(a) \rfloor \bmod 2 = 1$ (for $k \ge 1$ this is the $k$-th binary digit of $p(a)$; a leaf at depth $0$ occurs only when $p(a) = 1$). Equivalently, it outputs $a$ within the first $k$ flips with probability exactly $\lfloor 2^k p(a)\rfloor / 2^k$. Its expected number of flips equals $\sum_{a \in \alpha} \nu(p(a))$, where $\nu(x) = \sum_{n \ge 0} \bigl(x - \lfloor 2^n x \rfloor / 2^n\bigr)$ is the total binary truncation error of $x \in [0,1]$.

## Depends on

- [Discrete distribution generating (DDG) tree](ddg-tree.md)
- [Kraft's inequality for prefix codes](../../../InformationTheory/source-coding/kraft-mcmillan-lengths.md)

## Sources

- Donald E. Knuth and Andrew C. Yao, "The Complexity of Nonuniform Random Number Generation", in Algorithms and Complexity: New Directions and Recent Results, Academic Press, 1976.
- Thomas M. Cover and Joy A. Thomas, "Elements of Information Theory", 2nd ed., Wiley-Interscience, 2006.
