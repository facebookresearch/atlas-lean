# Win probability of a threshold rule in the secretary problem

For natural numbers $n$ and $r$, $P_r = (1 + (r - 1) T_r)/n$, with $T_r = \sum_{j=r}^{n-1} 1/j$
the [harmonic tail](harmonic-tail.md) (and $P_r = 0$ for $n = 0$). For $n$ applicants and a
threshold $2 \le r \le n$ this is Ferguson's equation (3),
$P_r = \frac{r-1}{n} \sum_{k=r}^{n} \frac{1}{k-1}$, and $P_1 = 1/n$ is his value for $r = 1$.

The uniform form agrees with Ferguson's (3), $\frac{r-1}{n} \sum_{k=r}^{n} \frac{1}{k-1} = \frac{r-1}{n} \big( \frac{1}{r-1} + T_r \big)$ for $2 \le r \le n$, and with his value $P_1 = 1/n$; for $r > n$ the formula is only algebraic (for $n = 1$ and $r = 2$ it gives $1$, while Ferguson's empty sum gives $0$). For $1 \le r \le n$ it is the win probability of $N_r$ for uniformly random interview orders: [the random-order model](card-threshold-rule-wins-div-factorial.md). For $n = 4$ it gives $P_2 = 11/24 \approx .458$, as in Ferguson's table.

## Sources

- T. S. Ferguson, *Optimal Stopping and Applications*, online text (UCLA Department of Mathematics), Chapter 2, §2.1, equation (3) and the table that follows it.
