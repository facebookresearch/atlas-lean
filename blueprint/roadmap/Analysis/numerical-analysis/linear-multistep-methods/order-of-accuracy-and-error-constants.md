# Order of accuracy and error constants of a linear multistep method

Let a [linear $k$-step method](linear-multistep-method.md) with coefficients $\alpha_j, \beta_j$ have $\sigma(1) \ne 0$, and let $T_n$ be its [truncation error](truncation-error-and-consistency.md). The method has *order of accuracy* $p$ if $p$ is the largest positive integer such that, for every sufficiently smooth solution curve of the initial value problem in the rectangle $R$, there are constants $K$ and $h_0 > 0$ with

$$|T_n| \le K h^p \qquad \text{for } 0 < h \le h_0$$

and every $k + 1$ consecutive mesh points $(x_n, y(x_n)), \dots, (x_{n+k}, y(x_{n+k}))$ on the curve.

Its *error coefficients* are the numbers

$$C_0 = \sum_{j=0}^{k} \alpha_j, \qquad C_q = \sum_{j=0}^{k} \Bigl(\frac{j^q}{q!}\, \alpha_j - \frac{j^{q-1}}{(q-1)!}\, \beta_j\Bigr) \quad (q \ge 1),$$

with $0^0 = 1$, so that $C_1 = \sum_j j\alpha_j - \sum_j \beta_j = \rho'(1) - \sigma(1)$. They are the coefficients of the Taylor expansion $h\sigma(1) T_n = C_0 y(x_n) + C_1 h y'(x_n) + C_2 h^2 y''(x_n) + \cdots$. For a method of order $p$, the number $C_{p+1}$ is its *error constant*.

## Depends on

- [Truncation error and consistency of a linear multistep method](truncation-error-and-consistency.md)
- [Linear multistep method](linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.3, expansion (47) with the formulas for $C_0, C_1, \dots, C_q$, and Definition 6 with the paragraph after it. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
