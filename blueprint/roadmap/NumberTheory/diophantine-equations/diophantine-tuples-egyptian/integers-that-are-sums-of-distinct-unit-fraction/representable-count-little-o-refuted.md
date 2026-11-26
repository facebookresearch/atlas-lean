# Integers that are sums of distinct unit fractions are not o(log N) in number

It is not the case that $F(N) = o(\log N)$ as $N \to \infty$, where $F(N)$ is the number of positive integers that are sums of distinct unit fractions $1/n$ with $n \in \{1, \dots, N\}$.

This refutes [Erdős Problem 309, second question](representable-count-little-o.md), the statement recorded as a proposition; the refutation is due to Yokota (1990), whose lower bound $F(N) \ge (1/2 - o(1)) \log N$ already excludes $o(\log N)$. The later works cited under Sources sharpen the bound towards $\log N$; that asymptotic does not follow from the 1990 bound.

## Sources

- T. F. Bloom, Erdős Problems, Problem #309, https://www.erdosproblems.com/309.
- H. Yokota, On number of integers representable as sums of unit fractions, Canad. Math. Bull. 33 (1990), https://doi.org/10.4153/CMB-1990-037-0.
- H. Yokota, On number of integers representable as a sum of unit fractions. II, J. Number Theory (1997), 162–169.
- E. S. Croot III, On some questions of Erdős and Graham about Egyptian fractions, Mathematika (1999), 359–372.
