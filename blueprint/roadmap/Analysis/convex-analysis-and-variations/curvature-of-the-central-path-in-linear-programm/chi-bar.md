# Condition number χ̄ of a matrix

For a real $m \times n$ matrix $A$, $\bar\chi_A$ is the supremum (Mathlib's real $\mathrm{sSup}$) of
$\|G^{-1} A\|$ over the nonsingular $m \times m$ submatrices $G$ of $A$, where $G$ consists of the columns of
$A$ listed by an injection $J : \{1, \dots, m\} \to \{1, \dots, n\}$ and $\|\cdot\|$ is the operator norm
induced by the Euclidean norms. There are finitely many such $G$, so when $A$ has full row rank $m$ (at least
one $G$ is nonsingular) this is the maximum of the Oberwolfach report's definition (Monteiro–Tsuchiya,
Prop. 2.3(b)). When no $G$ is nonsingular, for example for the zero matrix with $m \ge 1$, the set is empty
and the value is $0$ by Mathlib's convention, not a classical condition number.
