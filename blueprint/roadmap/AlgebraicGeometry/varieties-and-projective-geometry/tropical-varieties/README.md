# Tropical varieties

Over a field $K$ with a valuation $\mathrm{val} : K \to \mathbb{R} \cup \{\infty\}$, a Laurent polynomial $f = \sum_u c_u x^u$ tropicalizes to the piecewise-linear function $\operatorname{trop}(f)(w) = \min_{u : c_u \neq 0} (\mathrm{val}(c_u) + u \cdot w)$ on $\mathbb{R}^n$, and its tropical hypersurface is where this minimum is attained at least twice. When $K$ is algebraically closed and the valuation is nontrivial, Kapranov's theorem identifies the tropical hypersurface of a nonzero $f$ with the closure of the coordinatewise valuations of the zeros of $f$ in the torus $(K^*)^n$. The tropicalization of an ideal $I$ of Laurent polynomials is the intersection of the tropical hypersurfaces of its nonzero polynomials (so the zero ideal tropicalizes to $\mathbb{R}^n$), and under the same hypotheses on $K$ the Fundamental Theorem of tropical algebraic geometry identifies it, in the same way, with the closure of the valuations of the points of the variety $V(I)$.

- [Laurent polynomials](laurent-poly.md)
- [Value of one term of a tropical polynomial](trop-term.md)
- [Tropical hypersurface](tropical-hypersurface.md)
- [Evaluation of a Laurent polynomial on the torus](eval-torus.md)
- [Coordinatewise valuations of a hypersurface](valuations-of-zeros.md)
- [Kapranov's theorem](tropical-hypersurface-eq-closure-valuati.md)
- [Tropicalization of an ideal of Laurent polynomials](tropical-variety.md)
- [Coordinatewise valuations of a variety](valuations-of-variety.md)
- [Fundamental Theorem of Tropical Algebraic Geometry](tropical-variety-eq-closure-valuations-o.md)

## Related topics

- [Bernstein's theorem on sparse polynomial systems](../bernstein-s-theorem-on-sparse-polynomial-systems/README.md): Newton polytopes and mixed volumes, the polyhedral side of the same picture; tropical hypersurfaces are dual to regular subdivisions of Newton polytopes.
- [Newton polygon](../../../Algebra/polynomials/newton-polygon/README.md): the Newton polygon of a bivariate polynomial, whose regular subdivisions are dual to plane tropical curves.
- [Valuation rings](../../../RingTheory/valuation-rings/README.md): the valued fields over which tropicalization is defined.
- [Gröbner bases](../../../RingTheory/ideals-and-constructions/gr-bner-bases/README.md): the initial ideals $\mathrm{in}_w(I)$ of the second description of a tropical variety in the Fundamental Theorem come from Gröbner theory with weight vectors.
