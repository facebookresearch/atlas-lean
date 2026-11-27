# Kapranov's theorem

Let $K$ be an algebraically closed field with a nontrivial valuation
$\mathrm{val} : K \to \mathbb{R} \cup \{\infty\}$, and let $f = \sum_u c_u x^u$ be a nonzero
Laurent polynomial in $n$ variables over $K$. The tropical hypersurface of $f$, the set of
$w \in \mathbb{R}^n$ where the minimum $\min_{u : c_u \neq 0} (\mathrm{val}(c_u) + u \cdot w)$ is
attained at least twice, equals the closure in $\mathbb{R}^n$ of the set of coordinatewise
valuations $(\mathrm{val}(y_1), \dots, \mathrm{val}(y_n))$ of the zeros $y \in (K^*)^n$ of $f$.

So a purely combinatorial object, computed from the valuations of the coefficients alone, records
where the points of the classical hypersurface lie at the scale of the valuation. Maclagan and
Sturmfels state the theorem as the coincidence of three sets, the second being described by
initial forms; the statement above is the equality of the first and the third. It is the base
case of the Fundamental Theorem of tropical algebraic geometry, which replaces $f$ by an arbitrary
ideal of Laurent polynomials.

The hypothesis $f \neq 0$ is implicit in the source: for $f = 0$ the tropical hypersurface is
empty while every point of the torus is a zero.

## Sources

- Diane Maclagan and Bernd Sturmfels, *Introduction to Tropical Geometry*, draft of 4 November 2009, Definition 3.1.1 and Theorem 3.1.3, under the standing assumption of Chapter 3. Published as Graduate Studies in Mathematics 161, American Mathematical Society, 2015, Section 3.1.
