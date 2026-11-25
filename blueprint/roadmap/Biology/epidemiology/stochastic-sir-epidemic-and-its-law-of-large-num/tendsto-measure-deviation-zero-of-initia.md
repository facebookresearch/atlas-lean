# Deterministic initial counts with convergent scaled values satisfy Kurtz's initial condition

Let $\mu$ be a measure on $\Omega$, not necessarily a probability measure. For each natural
number $N$ let $S_N, I_N, R_N$ be random paths $\mathbb{R} \to \mathbb{N}$ on $\Omega$, and let $s$,
$i$, $r$ be real functions. Suppose there are natural numbers $S_0(N)$, $I_0(N)$, $R_0(N)$ such
that, for every $N$, $S_N(0) = S_0(N)$, $I_N(0) = I_0(N)$ and $R_N(0) = R_0(N)$ hold
$\mu$-almost everywhere, and

$$S_0(N)/N \to s(0), \qquad I_0(N)/N \to i(0), \qquad R_0(N)/N \to r(0) \qquad (N \to \infty).$$

Then for every $\delta > 0$, $\mu(D_N(0) \ge \delta) \to 0$ as $N \to \infty$, where $D_N(0)$ is the
[deviation](deviation.md) at time $0$ of $(S_N, I_N, R_N)/N$ from $(s, i, r)$; the event is not
assumed measurable, and $\mu$ is applied to it as an outer measure. For a probability
measure this is the hypothesis of
[Kurtz's law of large numbers](tendsto-measure-deviation.md) that the scaled initial state
converges in probability to $(s(0), i(0), r(0))$.
