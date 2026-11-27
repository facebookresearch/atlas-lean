# Error and magnitude bounds for rounded summation

For a precision $p$ and real numbers $x_1, \dots, x_n$, let $\hat s$ be their recursively rounded sum, each partial sum rounded by $\mathrm{fl}_p$ (to nearest at $p$ significant bits, ties to even), and let $u = 2^{-p}$. Then

$$\Big|\hat s - \sum_i x_i\Big| \le \big((1 + u)^n - 1\big) \sum_i |x_i| \quad\text{and}\quad |\hat s| \le (1 + u)^n \sum_i |x_i|.$$
