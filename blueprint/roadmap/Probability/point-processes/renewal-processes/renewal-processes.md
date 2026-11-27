# Renewal processes

A *renewal process* is a sequence of times $0 = t_0 \le t_1 \le t_2 \le \cdots$ whose interarrival times $X_n = t_n - t_{n-1}$, $n \ge 1$, are i.i.d. nonnegative random variables with $P(X_1 > 0) > 0$, and hence $t_n \to \infty$ almost surely. Here $t_n = X_1 + \cdots + X_n$ is the $n$-th renewal epoch and $N(t) = \max\{n : t_n \le t\}$ is the number of indices $n \ge 1$ with $t_n \le t$, renewals at time $0$ included and the distinguished $t_0$ not counted; when the interarrival times are positive, it is the number of renewals in $(0, t]$. The *rate* of the process is $\lambda = 1/E[X_1] \in [0, \infty)$; the process is *positive recurrent* when $0 < E[X_1] < \infty$ and *null recurrent* when $E[X_1] = \infty$. A Poisson process of rate $\lambda$ is the renewal process with exponential interarrival times of mean $1/\lambda$.

## Sources

- K. Sigman, *Some basic renewal theory: the renewal reward theorem*, lecture notes, IEOR 4106, Columbia University, 2018, <http://www.columbia.edu/~ks20/4106-18-Fall/Notes-RRT.pdf>, Section 1.1 and Remark 1.
