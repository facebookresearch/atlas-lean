# Higher-order Bernoulli numbers

For a complex number $\alpha$ and a natural number $n$, the
higher-order Bernoulli number $B_n^{(\alpha)}$ is $n!$ times the coefficient of $t^n$ in the
formal power series $\left(t / (e^t - 1)\right)^{\alpha}$. Here $t / (e^t - 1)$ is the Bernoulli
generating series $\sum_{k \ge 0} B_k t^k / k!$ (with $B_1 = -1/2$), and its $\alpha$-th power is
the binomial series $(1 + u)^{\alpha} = \sum_{j \ge 0} \binom{\alpha}{j} u^j$ with
$u = t / (e^t - 1) - 1$ substituted.

Equivalently, $B_n^{(\alpha)} = B_n^{(\alpha)}(0)$, where the generalized Bernoulli polynomials
$B_n^{(\alpha)}(x)$ are given by the exponential generating function
$\sum_{n \ge 0} B_n^{(\alpha)}(x) t^n / n! = \left(t / (e^t - 1)\right)^{\alpha} e^{tx}$.

## Sources

- Redha Chellal, Farid Bencherif, and Mohamed Mehbali, *An Identity for Generalized Bernoulli Polynomials*, Journal of Integer Sequences 23 (2020), Article 20.11.2, Section 1, equations (1) and (2), <https://cs.uwaterloo.ca/journals/JIS/VOL23/Chellal/chellal7.html>.
