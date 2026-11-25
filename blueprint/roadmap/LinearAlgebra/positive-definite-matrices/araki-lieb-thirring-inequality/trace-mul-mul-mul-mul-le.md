# $\operatorname{tr}((XY)^2) \le \operatorname{tr}(X^2Y^2)$ for Hermitian matrices

For Hermitian complex square matrices $X$ and $Y$,
$\operatorname{tr}(XYXY) \le \operatorname{tr}(XXYY)$, both traces being real: the difference is the
nonnegative real number $\tfrac12 \operatorname{tr}(C^* C)$ with $C = XY - YX$. It is the case `t = 2` of the Lieb–Thirring trace inequality
(E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes
draft of May 3, 2009, Theorem 7.4) and the first step of the usual proof of the Golden–Thompson
inequality.

For the Pauli matrices $\sigma_z, \sigma_x$ the two sides are $-2$ and $2$, so the inequality can be strict; equality holds exactly when $X$ and $Y$ commute, since the gap is $\tfrac12\|XY - YX\|_F^2$, where $\|\cdot\|_F$ is the Frobenius norm. The usual proof of the Golden–Thompson inequality extends this to $\operatorname{tr}((XY)^{2^k}) \le \operatorname{tr}((X^2Y^2)^{2^{k-1}})$ for positive $X, Y$ and combines it with the Lie–Trotter formula; the inequality above is the first step, $k = 1$.

## Informally uses

- [Commutator identity for traces](trace-commutator-conj-transpose-mul-self.md): the gap is $\operatorname{tr}(C^* C)/2 \ge 0$.

## Background

- [Golden–Thompson inequality](../golden-thompson-inequality/golden-thompson.md): the inequality whose usual proof starts with this step.

## Sources

- E. A. Carlen, Trace inequalities and quantum entropy: an introductory course, lecture-notes draft of May 3, 2009, Theorem 7.4 (the case $t = 2$). Theorem numbers refer to that draft.
