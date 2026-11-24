# Argument principle on a piecewise-smooth Jordan contour

Let $\Gamma$ be a piecewise continuously differentiable Jordan curve in $\mathbb{C}$, positively oriented, and let $D$ be the bounded component of $\mathbb{C} \setminus \Gamma$. Let $f$ be meromorphic on an open set containing $D \cup \Gamma$, with no zeros or poles on $\Gamma$. Let $Z$ and $P$ be the numbers of zeros and poles of $f$ in $D$, counted with multiplicity. Then

$$\frac{1}{2\pi i}\oint_\Gamma \frac{f'(z)}{f(z)}\, dz = Z - P,$$

and this number is the winding number about $0$ of the closed curve $f \circ \Gamma$, that is, $\frac{1}{2\pi}$ times the net change of a continuous argument of $f$ along $\Gamma$. Traversing $\Gamma$ clockwise changes the sign. The Nyquist contour, an interval of the imaginary axis with small semicircular indentations closed by a large half-circle, is such a curve.

## Expansion

The proof combines Cauchy's theorem on the Jordan domain $D$ with the residue of $f'/f$ at a zero or pole of order $m$, which is $m$ or $-m$. Beyond the [argument principle on a closed disc](argument-principle-closed-ball-general.md), the general Jordan-domain version needs the Jordan curve theorem for piecewise-smooth curves and Cauchy's theorem for their interiors, or, for the Nyquist contour in particular, a decomposition of the half-disc with indentations into finitely many convex pieces.

## Depends on

- [Argument principle on a closed disc](argument-principle-closed-ball-general.md): the disc case, which this statement extends to piecewise-smooth Jordan contours

## Sources

- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021 (electronic edition v3.0i, <http://fbsbook.org>), Section 10.2, Theorem 10.3 (principle of variation of the argument: for a closed bounded region $D$ with boundary $\Gamma$ and $f$ analytic in $D$ and on $\Gamma$ except at finitely many poles and zeros, the winding number is $\frac{1}{2\pi}\Delta\arg_\Gamma f = \frac{1}{2\pi i}\oint_\Gamma f'/f = Z - P$, p. 10-11).
