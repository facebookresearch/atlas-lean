# Navon-Samorodnitsky: LP bounds from eigenvalues of subsets of the cube

Let $\lambda(B)$ denote the largest eigenvalue of the adjacency matrix of the hypercube $\{0,1\}^n$ restricted to a set $B$. If $\lambda(B) \ge n - 2d + 1$, then every binary code $C$ of minimum distance $d$ satisfies $|C| \le \mathrm{poly}(n)\cdot |B|$. Taking $B$ a Hamming ball of radius $r<n/2$, with $\lambda(B) = (2+o(1))\sqrt{r(n - r)}$ as $n \to \infty$ with $r/n$ fixed, recovers the first MRRW bound.

## Proof sketch

Let $f \ge 0$ be the Perron eigenfunction of $B$. Consider $F = \sum_{c \in C} f(\cdot + c)$, and compare $\langle F, A F\rangle$ (with $A$ the cube adjacency matrix) against $\lambda(B)\|F\|^2$. Distinct translates interact only through Fourier coefficients on high levels, which the minimum distance forces to be small in the averaged sense of the Delsarte inequalities; comparing the resulting upper and lower estimates for $\langle F, AF \rangle$ gives $|C| \le \mathrm{poly}(n)|B|$.

## Proof depends on

- [Delsarte's linear programming bound](delsarte-linear-programming-bound.md)
- [Binary Krawtchouk polynomials](binary-krawtchouk-polynomials.md)

## Sources

- Michael Navon, Alex Samorodnitsky, "Linear programming bounds for codes via a covering argument", Discrete and Computational Geometry 41 (2009).
- Joel Friedman, Jean-Pierre Tillich, "Generalized Alon-Boppana theorems and error-correcting codes", SIAM Journal on Discrete Mathematics 19(3) (2005).
