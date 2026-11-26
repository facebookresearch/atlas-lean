# Interval arithmetic operations

For [intervals](interval.md) $X$ and $Y$ and an operation $\circ \in \{+, -, \times\}$, define

$$X \circ Y = \{x \circ y : x \in X,\ y \in Y\},$$

and, when $0 \notin Y$, $X \div Y = \{x / y : x \in X,\ y \in Y\}$. Each of these sets is again an interval, since it is the image of the compact connected set $X \times Y$ under a continuous map. Explicitly,

$$[a,b] + [c,d] = [a + c,\ b + d], \qquad [a,b] - [c,d] = [a - d,\ b - c],$$

and $[a,b] \times [c,d] = [\min P, \max P]$ for the set $P = \{ac, ad, bc, bd\}$ of endpoint products. Each operation is a set extension of the corresponding real operation: it contains $x \circ y$ for every $x \in X$ and $y \in Y$.

## Depends on

- [Interval](interval.md)

## Sources

- M. H. van Emden and B. Moa, *The fundamental theorems of interval analysis*, arXiv:cs/0701141v2, 2009, Section 3, display (2) and Definition 6 (interval operations as hulls of the sets of pointwise results, which for bounded intervals and exact arithmetic are the sets above), display (3) (the endpoint form of addition), and Theorem 1 (the operations are set extensions of the real operations). <https://arxiv.org/abs/cs/0701141>
