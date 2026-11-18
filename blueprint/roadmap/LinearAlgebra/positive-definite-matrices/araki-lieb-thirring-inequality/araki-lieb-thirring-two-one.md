# Lieb–Thirring trace inequality for `t = 2`

For positive semidefinite complex matrices $A$ and $B$, $\operatorname{tr}\bigl((A^{1/2} B A^{1/2})^2\bigr) \le \operatorname{tr}(A B^2 A)$; both traces are real. This is the instance $r = 2$, $q = 1$ of the Araki–Lieb–Thirring inequality (H. Araki, Lett. Math. Phys. 19 (1990) 167–170; K. M. R. Audenaert, arXiv:math/0701129, Theorem 1), in the form of the [general statement](araki-lieb-thirring.md), and the case $t = 2$ of the Lieb–Thirring trace inequality (E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 7.4). Matrix powers are defined by the functional calculus, and both sides reduce to $\operatorname{tr}(ABAB) \le \operatorname{tr}(AABB)$.

The proof squares out both functional-calculus powers: with $S = A^{1/2}$ one has $S^2 = A$, so $\operatorname{tr}(S B S)^2 = \operatorname{tr}(ABAB)$, while the right side is $\operatorname{tr}(A B^2 A) = \operatorname{tr}(A^2 B^2)$. The inequality is then $\operatorname{tr}(XY)^2 \le \operatorname{tr}X^2Y^2$ for Hermitian $X, Y$.

## Informally uses

- [`tr (XY)² ≤ tr X²Y²` for Hermitian matrices](trace-mul-mul-mul-mul-le.md): the inequality to which both sides reduce.

## Background

- [Araki–Lieb–Thirring inequality](araki-lieb-thirring.md): the general statement, of which this is the instance $r = 2$, $q = 1$.

## Sources

- E. A. Carlen, Trace inequalities and quantum entropy: an introductory course, lecture-notes draft of May 3, 2009, Theorem 7.4. Theorem numbers refer to that draft.
- K. M. R. Audenaert, On the Araki–Lieb–Thirring inequality, arXiv:math/0701129, Theorem 1.
