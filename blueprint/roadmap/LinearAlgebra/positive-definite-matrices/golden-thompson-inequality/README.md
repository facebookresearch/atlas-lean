# Golden–Thompson inequality

For Hermitian complex square matrices $A$ and $B$, $\operatorname{tr} e^{A+B} \le \operatorname{tr}(e^A e^B)$; both sides are real numbers.

## Idea

For numbers, or commuting matrices, $e^{A+B} = e^A e^B$ and the two sides are equal. For noncommuting Hermitian matrices the identity fails, but the trace still satisfies the inequality, which can be strict. The usual proof writes $e^{A+B} = \lim_m (e^{A/m}e^{B/m})^m$ by the Lie–Trotter formula and bounds the trace of the product by repeated use of $\lvert\operatorname{tr}((XY)^{2m})\rvert \le \operatorname{tr}((X^2Y^2)^m)$ for Hermitian $X$, $Y$ and $m$ a power of $2$. Golden and Thompson proved it independently in 1965 for statistical mechanics, where it bounds a partition function. It is also an early tool in matrix concentration inequalities, later sharpened by Lieb's concavity theorem.

## Statements

- [Golden–Thompson inequality](golden-thompson.md)
- [Golden–Thompson inequality for commuting matrices](golden-thompson-of-commute.md): special case: commuting matrices
- [Golden–Thompson equality for commuting matrices](trace-exp-add-of-commute.md): for commuting matrices it is an equality
- [The right side of Golden–Thompson is a nonnegative real](trace-exp-mul-exp-nonneg.md): the right side is a nonnegative real number

## Background

- [Araki–Lieb–Thirring inequality](../araki-lieb-thirring-inequality/README.md): its case $q = 1$, the Lieb–Thirring trace inequality, is the step from which the usual proof of Golden–Thompson starts.

## Related topics

- [Exponential limits and the Lie–Trotter formula](../../../Analysis/operator-algebras/exponential-limits-and-the-lie-trotter-formula/README.md): the product formula used in the usual proof.
- [Peierls and Klein inequalities](../../../Analysis/operator-theory/eigenvalue-inequalities/peierls-and-klein-inequalities/README.md): the other classical trace-exponential bounds, including Peierls–Bogoliubov.
