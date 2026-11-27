# LLL-reduced bases approximate the shortest lattice vector

Let $\frac14 < \delta \le 1$ and let $b_0, \dots, b_n$ be $\delta$-reduced (size reduced, $|\mu_{ij}| \le \frac12$, and satisfying the Lovász condition at every index). Then for every nonzero $x$ in the integer span of the $b_i$,

$$
\|b_0\|^2 \le \Big(\frac{4}{4\delta - 1}\Big)^{n} \|x\|^2 ;
$$

for $\delta = 3/4$ this is $\|b_0\| \le (\sqrt{2})^{n}\|x\|$. On linearly independent integer rows, the LLL algorithm with $\delta = 3/4$ outputs a $3/4$-reduced basis of the same lattice.

## Proof sketch

Reducedness gives $\|b_{i+1}^*\|^2 \ge (\delta - \frac14)\|b_i^*\|^2$, so $\|b_0\|^2 \le (4/(4\delta-1))^{n}\|b_j^*\|^2$ for every $j$; every nonzero lattice vector has norm at least $\min_j \|b_j^*\|$.

## Depends on

- [The LLL potential](lll-potential.md)
- [The Lenstra–Lenstra–Lovász algorithm](../lattice-basis-reduction/the-lenstralenstralovasz-algorithm.md)

## Proof depends on

- [Bounds on the LLL potential and the number of exchanges](lll-potential-bounds.md)

## Sources

- A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, "Factoring Polynomials with Rational Coefficients", Mathematische Annalen 261(4), 1982.
- O. Regev, "Lattices in Computer Science", lecture notes, Tel Aviv University, 2004.
