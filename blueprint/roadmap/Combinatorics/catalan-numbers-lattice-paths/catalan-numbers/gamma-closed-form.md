# Closed form of the Eloe–Kublik gamma array

Let $\gamma_{n,k}$, for natural numbers $n$ and
$k$, be real numbers such that $\gamma_{n,0} = 1$ for every $n$, $\gamma_{2n-1,n} = 0$ for every
$n \ge 1$, and

$$\gamma_{n,k} = (1 + \frac{2k}{n+2})\,\gamma_{n-1,k} + \frac{2k-n-1}{n+2}\,\gamma_{n-1,k-1}$$

whenever $n \ge 2$ and $1 \le k \le \lfloor n/2 \rfloor$. Then
$\gamma_{n,k} = (-\frac{1}{4})^k \binom{n}{2k} C_k$ for all natural numbers $n$ and $k$ with
$k \le \lfloor n/2 \rfloor$, where $C_k$ is the $k$-th Catalan number.

## Sources

- Paul Eloe and Catherine Kublik, "When Numerical Analysis Crosses Paths with Catalan and Generalized Motzkin Numbers," Journal of Integer Sequences 21 (2018), Article 18.8.4, Theorem `closedform_thm`, lines 390-396, <https://cs.uwaterloo.ca/journals/JIS/VOL21/Kublik/kublik2.tex>; the recursion and initial conditions are equation `gamma_linear_recursion`, lines 87-91.
