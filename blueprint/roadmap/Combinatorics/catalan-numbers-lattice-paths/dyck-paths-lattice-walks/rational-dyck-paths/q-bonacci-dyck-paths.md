# The $Q$-bonacci paths $Q_n^{r/s}$

For natural numbers $r$, $s$ and $n$, $Q_n^{r/s}$ is
the finite set of Dyck paths of semilength $n$ and height at most $2$ that satisfy the following
run condition. For $n \ge 1$ such a path factors as $U X_1 \cdots X_{n-1} D$ with each $X_i$
either a $1$-peak $UD$ or a $0$-valley $DU$, and its block word $X_1 \cdots X_{n-1}$ (empty for
$n = 0$) splits into maximal runs of equal blocks. Every run of $p$ consecutive $1$-peaks must
have $p \le r$, and also $p s \le r v$, where $v$ is the length of the run of $0$-valleys
immediately after it ($v = 0$ if no run follows it); for the last run of $1$-peaks, the
inequality $p s \le r v$ is required only when $p < r$ and $v \ne 0$.

## Sources

- Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.3.2, Definition 4.
