# Polynomially weighted binomial sums of powers of a second-order sequence

Let $a$, $b$ be
real numbers and $(U_n)_{n \ge 0}$ a real sequence with $U_{n+2} = a U_{n+1} + b U_n$ for all $n$.
Let $\alpha \ne \beta$ be complex numbers with $\alpha + \beta = a$ and $\alpha\beta = -b$ (the
roots of $y^2 = ay + b$), and put $A = (U_1 - U_0\beta)/(\alpha - \beta)$ and
$B = (U_1 - U_0\alpha)/(\alpha - \beta)$. Let $S(j, i)$ denote the Stirling numbers of the second
kind and $(N)_i = N(N-1)\cdots(N-i+1)$ the falling factorial. Let $c_0, c_1, c_2, \dots$ be
complex numbers, $t$, $N$, $r$ natural numbers and $h(y) = \sum_{j=0}^{t} c_j y^j$. Then for every
complex number $x$,

$$\sum_{k=0}^{N} h(k) \binom{N}{k} U_k^r x^k =
\sum_{j=0}^{t} c_j \sum_{i=0}^{j} S(j, i)\, x^i \sum_{\ell=0}^{r} \binom{r}{\ell} A^\ell
(-B)^{r-\ell} (N)_i\, (\alpha^\ell \beta^{r-\ell})^i (1 + \alpha^\ell \beta^{r-\ell} x)^{N-i}.$$

The source prints $A^j$, with the outer index $j$, where its proof gives $A^\ell$; the printed
form fails for the Fibonacci numbers $U_k = F_k$, $h = 1$, $r = N = 1$, $x = 0$ (left side $0$,
printed right side $1 - 1/\sqrt{5}$). The source's coefficients $A_j$ of $h$ are renamed $c_j$,
and positivity of $r$, $N$, $t$ is dropped.

## Sources

- Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.8.
