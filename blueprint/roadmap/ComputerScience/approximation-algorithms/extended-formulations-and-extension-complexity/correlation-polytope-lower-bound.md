# Kaibel-Weltge: the correlation polytope has extension complexity at least (3/2)^n

For every $n \ge 1$ and every linearly ordered field, $3^n \le 2^n \cdot \mathrm{xc}(\mathrm{COR}(n))$, that is,

$$
\mathrm{xc}(\mathrm{COR}(n)) \ge (3/2)^n .
$$

## Proof sketch

By Yannakakis' theorem it suffices to bound the rectangle covering number of the non-unique-intersection support. Kaibel and Weltge show that a rectangle avoiding all uniquely intersecting pairs contains at most $2^n$ of the $3^n$ disjoint pairs $(a, b)$, while every disjoint pair must be covered.

## Depends on

- [The correlation polytope](correlation-polytope.md)

## Proof depends on

- [Yannakakis' factorization theorem](yannakakis-factorization-theorem.md)

## Sources

- V. Kaibel and S. Weltge, "A Short Proof that the Extension Complexity of the Correlation Polytope Grows Exponentially", Discrete & Computational Geometry 53(2), 2015.
- S. Fiorini, S. Massar, S. Pokutta, H. R. Tiwary and R. de Wolf, "Exponential Lower Bounds for Polytopes in Combinatorial Optimization", Journal of the ACM 62(2), 2015.
