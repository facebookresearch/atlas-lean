# Araki–Lieb–Thirring inequality

For positive semidefinite complex matrices $A$ and $B$ and real numbers $q \ge 0$ and $r \ge 1$,

$$\operatorname{tr}\bigl((A^{1/2} B A^{1/2})^{rq}\bigr) \le \operatorname{tr}\bigl((A^{r/2} B^r A^{r/2})^q\bigr),$$

where powers of positive semidefinite matrices are defined by the functional calculus, with $0^0 = 1$.

## Idea

For commuting matrices both sides equal $\operatorname{tr}(A^{rq} B^{rq})$. In general, raising to the power $r \ge 1$ inside the product, before taking the trace, can only increase it. With $q = 1$ and $r = t$ this is the Lieb–Thirring inequality $\operatorname{tr}\bigl((A^{1/2}BA^{1/2})^t\bigr) \le \operatorname{tr}(A^{t/2}B^tA^{t/2})$, proved by Lieb and Thirring in their work on moments of Schrödinger eigenvalues; Araki extended it to every $q \ge 0$, and the inequality reverses for $0 \le r \le 1$. The simplest case, $\operatorname{tr}(XYXY) \le \operatorname{tr}(X^2Y^2)$ for Hermitian $X$ and $Y$, follows from the positivity of $\operatorname{tr}(C^*C)$ for the commutator $C = XY - YX$. Combined with the Lie–Trotter product formula, the Lieb–Thirring case gives the Golden–Thompson inequality.

## Statements

- [Araki–Lieb–Thirring inequality](araki-lieb-thirring.md)
- [Araki–Lieb–Thirring inequality, reversed range](araki-lieb-thirring-of-le-one.md): the reversed inequality for $0 \le r \le 1$
- [Lieb–Thirring trace inequality for $r = 2$, $q = 1$](araki-lieb-thirring-two-one.md): the special case $r = 2$, $q = 1$
- [$\operatorname{tr}((XY)^2) \le \operatorname{tr}(X^2Y^2)$ for Hermitian matrices](trace-mul-mul-mul-mul-le.md): $\operatorname{tr}(XYXY) \le \operatorname{tr}(X^2Y^2)$, used for that case
- [Commutator identity for traces](trace-commutator-conj-transpose-mul-self.md): the commutator identity behind it

## Related topics

- [Golden–Thompson inequality](../golden-thompson-inequality/golden-thompson.md): follows from the Lieb–Thirring case and the Lie–Trotter formula.
