# Adams methods

Adams methods have first characteristic polynomial $z^k - z^{k-1}$, which makes all of them zero-stable. The Adams–Bashforth and Adams–Moulton methods choose the other coefficients by integrating over one step the polynomial interpolant of $f$ at the $k$ previous nodes, or at those nodes and the new endpoint, and have orders $k$ and $k + 1$; the two-step Adams–Bashforth method is the simplest explicit multistep method of order two.

- [Adams methods](adams-methods.md)
- [The two-step Adams–Bashforth method is zero-stable](two-step-adams-bashforth-method-is-zero-stable.md)
- [Orders, error constants and stability intervals of the Adams methods](orders-and-stability-intervals-of-adams-methods.md)

## Related topics

- [Second-order convergence of the two-step Adams-Bashforth method](../second-order-convergence-of-the-two-step-adams-bashforth-method.md)
