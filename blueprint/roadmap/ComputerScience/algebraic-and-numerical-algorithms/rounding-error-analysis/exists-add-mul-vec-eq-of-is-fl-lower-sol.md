# Backward error of floating-point forward substitution

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent, $u = 2^{-p}$ for the unit roundoff and $\gamma_k = k u / (1 - k u)$. A vector $\hat y \in K^n$ is computed from an $n \times n$ matrix $L$ and $b \in K^n$ by forward substitution in floating point when, for every $i < n$, $\hat y_i = \mathrm{fl}(\hat s^{(i)} / L_{ii})$, where $\hat s^{(i)}$ is obtained from $b_i$ by subtracting the rounded products $\mathrm{fl}(L_{ik} \hat y_k)$ for $k = 0, \dots, i - 1$ in this order, rounding each subtraction (so $\hat y_0 = \mathrm{fl}(b_0 / L_{00})$). Let $L$ be an $n \times n$ lower triangular matrix with nonzero diagonal entries, let $\hat y$ be computed from $L$ and $b$ by forward substitution in floating point, and let $n u < 1$. Then there is an $n \times n$ matrix $\delta L$ with

$$(L + \delta L)\,\hat y = b \quad \text{and} \quad |\delta L_{ik}| \le \gamma_n |L_{ik}| \text{ for all } i, k.$$

Triangular solves are thus backward stable componentwise, whatever the conditioning of $L$; this is homework 1.11 of J. W. Demmel's Math 221 course, recalled in the Lecture 5 notes (UC Berkeley, 2024) in first-order form $|\delta L| \le n\,\varepsilon\,|L|$; the exact form $\gamma_n|L|$ is the one of N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002, in the chapter on triangular systems. The perturbation keeps the zero pattern of $L$.

**Proof.** Row $i$ of the residual $b - L\hat y$ is bounded by $\gamma_{i+1} \sum_k |L_{ik}|\,|\hat y_k|$ by the [residual bound for one division step](abs-sub-sum-sub-mul-le.md), and $\gamma_{i+1} \le \gamma_n$; such a residual is a [componentwise perturbation](exists-perturbation-of-abs-le.md) of $L$.

## Informally uses

- [Residual bound for one division step](abs-sub-sum-sub-mul-le.md): one row of forward substitution.
- [Residuals as componentwise perturbations](exists-perturbation-of-abs-le.md): turns the row residuals into $\delta L$.
