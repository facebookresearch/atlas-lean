# Null distribution recursion and integral bounds for the rank product

**Setting.** $n$ molecules are profiled in $k$ independent (paired) experiments. Under the null hypothesis that a molecule is not differentially expressed, its rank $r_i$ in experiment $i$ is uniform on $\{1,\dots,n\}$, independently across experiments, and its **rank product** is $r_1r_2\cdots r_k$. Define

$$G_k(\rho) = \sum_{r_1=1}^n\cdots\sum_{r_k=1}^n \Theta\big(\rho - r_1r_2\cdots r_k\big), \qquad \Theta(x) = \mathbf 1[x \ge 0],$$

so that $G_k(\rho)/n^k$ is the null probability that the rank product is at most $\rho$ (the $p$-value of an observed rank product $\rho$). Then $G_k(\rho) = 0$ for $\rho < 1$ and $G_k(\rho) = n^k$ for $\rho \ge n^k$.

**Recursion.** Splitting off the first rank,

$$G_k(\rho) = \sum_{r_1=1}^n G_{k-1}(\rho/r_1) = G_{k-1}(\rho) + \sum_{r_1=2}^{\min(\rho,n)} G_{k-1}(\rho/r_1).$$

**Theorem (integral bounds).** Let $\overline G_k$ and $\underline G_k$ satisfy

$$\overline G_k(\rho) = \overline G_{k-1}(\rho) + \int_1^{\min(\rho,n)}\overline G_{k-1}(\rho/r)\,dr, \qquad \underline G_k(\rho) = \underline G_{k-1}\big(\max(1,\rho/n)\big) + \int_1^{\min(\rho,n)} \underline G_{k-1}(\rho/r)\,dr,$$

with $\overline G_0(\rho) = \underline G_0(\rho) = G_0(\rho) = \Theta(\rho - 1)$. Then for every $k \ge 0$ and $\rho \le n^k$,

$$\underline G_k(\rho) \le G_k(\rho) \le \overline G_k(\rho).$$

## Expansion

$G_k$ is non-decreasing in $\rho$, so $r \mapsto G_{k-1}(\rho/r)$ is non-increasing, and the sum over $r_1 = 2,\dots,\min(\rho,n)$ lies between the integral of the same function over $[1,\min(\rho,n)]$ and that integral shifted by the first or last term; an induction on $k$ carries the inequality through the recursion. The upper bound gives conservative $p$-values that protect against false positives, and the geometric mean of the two bounds is an accurate (though not guaranteed) approximation. Unlike the gamma approximation, which overstates small $p$-values by orders of magnitude, and unlike exact enumeration or permutation, which become infeasible for large $\rho$ or tiny $p$, the bounds are uniformly fast.

## Sources

- T. Heskes, R. Eisinga, R. Breitling, "A fast algorithm for determining bounds and accurate approximate p-values of the rank product statistic for replicate experiments", BMC Bioinformatics 15 (2014) 367, Methods, Eq (1) and Theorem 1 (proof in Additional file 1), <https://doi.org/10.1186/s12859-014-0367-1>, PMCID PMC4245829.
