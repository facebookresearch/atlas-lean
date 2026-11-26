# Eradication threshold for a sensitive–resistant switching tumour

Let $C_R(t), C_S(t) \ge 0$ be the sizes of a drug-resistant and a drug-sensitive tumour-cell population that switch phenotype at rates $w_{RS} \ge 0$ (resistant to sensitive) and $w_{SR} \ge 0$ (sensitive to resistant), with net growth rates $r_R = b_R - d_R$ and $r_S = b_S - d_S$ under therapy:

$$\frac{dC_R}{dt} = (r_R - w_{RS})\, C_R + w_{SR}\, C_S, \qquad \frac{dC_S}{dt} = (r_S - w_{SR})\, C_S + w_{RS}\, C_R.$$

**Proposition.** Assume the therapy is effective on the sensitive cells, $r_S < 0$, and set $\theta_S = w_{SR}/|r_S|$. The tumour-free state $(0,0)$ is asymptotically stable (every solution decays exponentially to $0$) if and only if

$$w_{RS} > w_{RS}^* = r_R\,(1 + \theta_S), \qquad\text{equivalently}\qquad r_R < r_R^* = \frac{w_{RS}}{1 + w_{SR}/|r_S|}.$$

If $w_{RS} < w_{RS}^*$, the matrix of the system has a positive eigenvalue, so $(0,0)$ is unstable. If moreover both switching rates are positive, $w_{RS}, w_{SR} > 0$, this eigenvalue has an eigenvector $(v_R, v_S)$ with $v_R, v_S > 0$, and from every nonzero nonnegative initial condition both populations grow exponentially at that rate, with a ratio $C_R/C_S$ converging to $v_R/v_S$, independent of the initial condition. (Without switching this can fail: for $w_{RS} = w_{SR} = 0$, $r_R = 1$, $r_S = -1$ the threshold inequality holds, but the solution from $(0,1)$ is $(0, e^{-t})$.) In particular, if $r_R > w_{RS}$, then no increase of the sensitive death rate $d_S$ and no reduction of $w_{SR}$ (switch inhibition) can make $(0,0)$ stable: only raising the resistant-to-sensitive transition rate above $r_R(1+\theta_S)$, or lowering $r_R$, does.

## Proof depends on

- [Perron–Frobenius theorem for irreducible nonnegative matrices](../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md): applied to $J + cI$ for the positive eigenvector.
- [Positive left Perron vector of an irreducible matrix](../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/positive-left-perron-vector.md): for convergence of the composition from arbitrary nonzero nonnegative data.

## Expansion

The system is $\dot C = J C$ with $J = \begin{pmatrix} r_R - w_{RS} & w_{SR} \\ w_{RS} & r_S - w_{SR}\end{pmatrix}$, a Metzler matrix. Its determinant is $\det J = r_R r_S - r_R w_{SR} - r_S w_{RS} = w_{RS}|r_S| - r_R(|r_S| + w_{SR})$ when $r_S < 0$, which is positive exactly when $w_{RS} > r_R(1 + \theta_S)$. If $\det J > 0$ the trace is negative: either $r_R \le 0$ and both diagonal entries are negative, or $r_R > 0$ and then $w_{RS} > r_R$. Hence $\det J > 0$ is equivalent to both eigenvalues having negative real part. When $\det J < 0$ the eigenvalues are real of opposite sign, and for $w_{RS}, w_{SR} > 0$ the Perron–Frobenius theorem, applied to the nonnegative irreducible matrix $J + cI$ with $c > \max(w_{RS} - r_R,\ w_{SR} - r_S)$, gives the positive eigenvalue $\lambda$ of $J$ a positive eigenvector, which fixes the asymptotic composition. For nonzero nonnegative initial data, $J + cI$ is a nonnegative irreducible matrix for $c$ large, so $e^{tJ}$ has positive entries for $t > 0$; projecting onto the positive left eigenvector of the dominant eigenvalue shows that $e^{-\lambda t}C(t)$ converges to a positive multiple of $(v_R, v_S)$. If $r_R > w_{RS}$, then $r_R > 0$, and since $\theta_S \ge 0$, $w_{RS}^* = r_R(1+\theta_S) \ge r_R > w_{RS}$, so $\det J < 0$ whatever $d_S$ and $w_{SR}$ are. (The comparison $w_{RS}^* \ge r_R$ uses $r_R \ge 0$.)

## Sources

- G. Aguadé-Gorgorió, S. Kauffman and R. Solé, "Transition therapy: tackling the ecology of tumor phenotypic plasticity", Bulletin of Mathematical Biology 84 (2022), article 24, <https://doi.org/10.1007/s11538-021-00970-9>, PMCID PMC8712307 (Section 2.2, equations (11)–(14)).
