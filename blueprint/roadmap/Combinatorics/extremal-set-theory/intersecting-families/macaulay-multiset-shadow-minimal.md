# Macaulay's theorem for monomials

Let $k \ge 0$ and let $A$ be a finite set of
monomials of degree $k + 1$ in the variables $x_0, x_1, x_2, \dots$, given by their exponent
vectors: finitely supported $a \colon \mathbb{N} \to \mathbb{N}$ with $\sum_j a_j = k + 1$.
Suppose that $|A| = \sum_{i=0}^{k} \binom{d_i}{i + 1}$ for natural numbers
$d_0 < d_1 < \dots < d_k$. Let the shadow $\partial A$ be the set of exponent vectors obtained
from some $a \in A$ by lowering one positive coordinate $a_j$ by $1$. Then $\partial A$ has at
least $\sum_{0 \le i \le k,\ d_i \ge 1} \binom{d_i - 1}{i}$ elements.

Terms with $d_i = 0$, which can occur only for $i = 0$, contribute nothing to the bound.

Proof: following Ábrego, Fernández-Merchant, and Llano, from a binomial-cascade split
inequality and induction on coordinate slices (their route from Theorem 1 to Theorem M).

## Sources

- Bernardo M. Ábrego, Silvia Fernández-Merchant, and Bernardo Llano, "An Inequality for Macaulay Functions," Journal of Integer Sequences 14 (2011), Theorem M, lines 215–223. Source: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Abrego/abrego2.tex>.
