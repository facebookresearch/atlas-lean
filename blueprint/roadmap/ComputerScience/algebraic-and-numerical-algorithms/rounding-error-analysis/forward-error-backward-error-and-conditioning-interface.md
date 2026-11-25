# Forward error, backward error and conditioning interface

Let $f : D \to R$ be a target map between normed spaces and $\hat f : D \to R$ a computed map. At $x \in D$, the absolute forward
error is $\lVert \hat f(x) - f(x) \rVert$ and, when $f(x) \ne 0$, the relative forward error divides by $\lVert f(x) \rVert$. The backward
error is $\inf\{\lVert \Delta x \rVert : x + \Delta x \in D,\ \hat f(x) = f(x + \Delta x)\} \in [0, \infty]$, with $\inf \emptyset = \infty$; the
relative version divides by $\lVert x \rVert$ when $x \ne 0$. An algorithm is backward stable with constant $c$ if its backward error is
at most $c\, u \lVert x \rVert$ for every input, with $u$ the unit roundoff. A conditioning bound on an admissible perturbation set
is a constant $\kappa$ with $\lVert f(x + \Delta) - f(x) \rVert \le \kappa \lVert \Delta \rVert$ for all admissible $\Delta$; this exact Lipschitz
form is distinct from the differential condition number.

## Expansion

A good expansion adds a page for the following definition, which this page does not state, and links it under the
dependency sections.

- Statement prerequisite: the mixed forward–backward error, which requires the computed value to satisfy
  $\hat f(x) + \Delta y = f(x + \Delta x)$ with both $\lVert \Delta y \rVert$ and $\lVert \Delta x \rVert$ small, as a variant of the backward
  error above.

## Sources

- CS 4220 lecture notes: review / introduction (Spring 2023) — D. Bindel, Cornell University CS 4220. <https://www.cs.cornell.edu/courses/cs4220/2023sp/lec/review.pdf> Sec. 3.6, Sensitivity, conditioning, and types of error.
