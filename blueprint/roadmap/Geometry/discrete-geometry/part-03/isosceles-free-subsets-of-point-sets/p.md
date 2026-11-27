# Largest guaranteed isosceles-free subset $P_d(n)$

For $d, n \in \mathbb{N}$, let $P_d(n)$ be the least, over all sets $S \subset \mathbb{R}^d$ of exactly $n$ points, of the largest size of an isosceles-free subset of $S$:

$$P_d(n) = \min_{\substack{S \subset \mathbb{R}^d \\ \lvert S \rvert = n}} \ \max \{\, \lvert A \rvert : A \subseteq S,\ A \text{ isosceles-free} \,\}.$$

A set $A$ is isosceles-free if there are no three distinct points $x, y, z \in A$ such that two of the distances $\lVert x - y \rVert$, $\lVert y - z \rVert$, $\lVert z - x \rVert$ are equal. If no $n$-point subset of $\mathbb{R}^d$ exists (only possible for $d = 0$, $n \ge 2$), the value is $0$ by convention.

Whenever an $n$-point set exists ($d \ge 1$ or $n \le 1$), every such set has an isosceles-free subset of size $P_d(n)$, and some such set has none larger.

## Sources

- T. F. Bloom, Erdős Problems, Problem #1207. https://www.erdosproblems.com/1207
