# Piecewise closed form of the rank product bounds

**Setting.** For $\Delta \in \{0,1\}$ consider the unified recursion

$$\tilde G_k(\rho) = \Delta\,\tilde G_{k-1}(\rho) + (1-\Delta)\,\tilde G_{k-1}\big(\max(1,\rho/n)\big) + \int_1^{\min(\rho,n)}\tilde G_{k-1}(\rho/r)\,dr, \qquad \tilde G_0(\rho) = \Theta(\rho-1),$$

which gives the lower bound for $\Delta = 0$ and the upper bound for $\Delta = 1$ on the rank-product count $G_k(\rho)$ for $n$ molecules and $k$ experiments.

**Theorem (piecewise recursion).** Write $\tilde G_k(\rho) = n^k$ for $\rho \ge n^k$, $\tilde G_k(\rho) = 0$ for $\rho < 1$, and $\tilde G_k(\rho) = \tilde G_{kj}(\rho)$ on $n^{k-j} \le \rho < n^{k-j+1}$, $j = 1,\dots,k$ (so $j = \lceil k - \log\rho/\log n\rceil$), with $\tilde G_{k0} \equiv n^k$. Then for $1 \le j \le k-1$

$$\tilde G_{kj}(\rho) = \Delta\,\tilde G_{k-1,j-1}(\rho) + (1-\Delta)\,\tilde G_{k-1,j}(\rho/n) + \int_1^{\rho/n^{k-j}}\tilde G_{k-1,j-1}(\rho/r)\,dr + \int_{\rho/n^{k-j}}^{n}\tilde G_{k-1,j}(\rho/r)\,dr,$$

and $\tilde G_{kk}(\rho) = \Delta\,\tilde G_{k-1,k-1}(\rho) + (1-\Delta) + \int_1^\rho \tilde G_{k-1,k-1}(\rho/r)\,dr$.

**Theorem (functional form).** Every piece has the closed form

$$\tilde G_{kj}(\rho) = \varepsilon_{kj} + \delta_{kj}\,\rho + \sum_m \gamma_{kj,m}\,\rho\Big(\log\frac{\rho}{n^{k-j+\beta_{kj,m}}}\Big)^{\alpha_{kj,m}},$$

and the parameters $(\alpha,\beta,\gamma,\delta,\varepsilon)$ obey explicit linear update rules in $(k,j)$ initialized at $\varepsilon_{k0} = n^k$, $\delta_{k0} = 0$ and empty $\alpha,\beta,\gamma$.

## Depends on

- [Null distribution recursion and integral bounds for the rank product](null-distribution-recursion-and-integral-bounds-for-the-rank-product.md)

## Expansion

Splitting at $\rho = n$ and at $\rho/r = n^{k-1-(j-1)}$ removes the nonlinear limits $\min(\rho,n)$ and $\max(1,\rho/n)$: each piece now integrates functions of the form $\rho(\log(\rho/\lambda))^\alpha$, and $\int (\rho/r)(\log(\rho/(r\lambda)))^\alpha dr$ is again of that form with $\alpha$ raised by one, which is why the family is closed under the recursion. Computing $\tilde G_{kj}$ requires only the nodes $(k',j')$ on a lattice above $(k,j)$, so a bound at any $\rho$ costs a number of operations polynomial in $k$ and independent of $\rho$ and $n$.

## Sources

- T. Heskes, R. Eisinga, R. Breitling, "A fast algorithm for determining bounds and accurate approximate p-values of the rank product statistic for replicate experiments", BMC Bioinformatics 15 (2014) 367, Theorems 2–4, Eqs (4)–(11) (proofs in Additional files 2–4), <https://doi.org/10.1186/s12859-014-0367-1>, PMCID PMC4245829.
