# Navon-Samorodnitsky: LP bounds from eigenvalues of subsets of the cube

Let $\lambda(B)$ denote the largest eigenvalue of the adjacency matrix of the hypercube $\{0,1\}^n$ restricted to a set $B$. If $\lambda(B) \ge n - 2d + 1$, then every binary code $C$ of minimum distance $d$ satisfies $|C| \le n\,|B|$. For a Hamming ball $B(r)$ of radius $r$, $\lambda(B(r)) \ge 2\sqrt{r(n - r)} - o(n)$; hence there is a radius $r \le n/2 - \sqrt{d(n-d)} + o(n)$ with $\lambda(B(r)) \ge n - 2d + 1$, so $|C| \le n\,|B(r)|$, which recovers the first MRRW bound.

## Proof sketch

Let $f \ge 0$ be the Perron eigenfunction of $B$. Consider $F = \sum_{c \in C} f(\cdot + c)$, and compare $\langle F, A F\rangle$ (with $A$ the cube adjacency matrix) against $\lambda(B)\|F\|^2$. Distinct translates interact only through Fourier coefficients on high levels, which the minimum distance forces to be small in the averaged sense of the Delsarte inequalities; comparing the resulting upper and lower estimates for $\langle F, AF \rangle$ gives $|C| \le n|B|$.

## Proof depends on

- [Delsarte's linear programming bound](delsarte-linear-programming-bound.md)
- [Binary Krawtchouk polynomials](binary-krawtchouk-polynomials.md)

## Sources

- Michael Navon, Alex Samorodnitsky, "Linear programming bounds for codes via a covering argument", Discrete and Computational Geometry 41 (2009); arXiv:math/0702425 (Proposition 1.1 and Lemma 1.4).
- Joel Friedman, Jean-Pierre Tillich, "Generalized Alon-Boppana theorems and error-correcting codes", SIAM Journal on Discrete Mathematics 19(3) (2005).
