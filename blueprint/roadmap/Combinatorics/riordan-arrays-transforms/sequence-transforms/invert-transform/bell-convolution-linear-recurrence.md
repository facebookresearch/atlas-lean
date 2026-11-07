# Linear recurrence for convolution powers of an INVERT sequence

Let $(c_m)_{m \ge 0}$ and
$(y_n)_{n \ge 0}$ be real sequences such that for every $n \ge 0$

$$y_n = \sum_{k=0}^{n} k! \sum_{j} \prod_{i=1}^{n+1} \frac{c_i^{j_i}}{j_i!},$$

where the inner sum runs over all tuples $(j_1, \dots, j_{n+1})$ of integers with
$0 \le j_i \le n$, $j_1 + j_2 + \dots + j_{n+1} = k$ and $j_1 + 2 j_2 + \dots + (n+1) j_{n+1} = n$.
Let $r \ge 1$ be an integer, and for $N \ge 0$ let $y^{(r)}_N$ be the sum of
$y_{a_1} y_{a_2} \cdots y_{a_r}$ over all tuples $(a_1, \dots, a_r)$ of nonnegative integers with
$a_1 + \dots + a_r = N$. Then for every $n \ge 1$

$$n \, y^{(r)}_n = \sum_{m=1}^{n} \bigl(n + m(r-1)\bigr) \, c_m \, y^{(r)}_{n-m}.$$

The hypothesis says that $y_n = \sum_{k=0}^{n} \frac{k!}{n!} B_{n,k}(1!\,c_1, 2!\,c_2, \dots)$
with the partial Bell polynomials $B_{n,k}$, that is, $y$ is the INVERT transform of $c$: as
formal power series in $z$, $\sum_{n \ge 0} y_n z^n = 1/(1 - \sum_{m \ge 1} c_m z^m)$. The value
$c_0$ plays no role.

## Sources

- Daniel Birmajer, Juan B. Gil, and Michael D. Weiner, "Linear Recurrence Sequences and Their Convolutions via Bell Polynomials," Journal of Integer Sequences 18 (2015), Article 15.1.2, Theorem, equation, lines 425–435, https://cs.uwaterloo.ca/journals/JIS/VOL18/Gil/gil3.tex
