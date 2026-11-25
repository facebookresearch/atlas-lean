# Stationary workload for stationary ergodic increments

Let $(Z_i)_{i \in \mathbb{Z}}$ be a two-sided stationary ergodic sequence of integrable real random variables with $E[Z_0] < 0$, let $V_0 = 0$ and $V_n = Z_0 + Z_{-1} + \dots + Z_{-(n-1)}$ for $n \ge 1$, and let $X'_0 = \sup_{n \ge 0} V_n$. Then $X'_0$ is almost surely finite, and the sequence defined by $X'_{n+1} = \max(0, X'_n + Z_{n+1})$ for $n \ge 0$ is stationary and ergodic, with $X'_n = \sup_{k \ge 0}(Z_n + Z_{n-1} + \dots + Z_{n-k+1})$. Moreover, for every real random initial value $X_0$, the solution of $X_{n+1} = \max(0, X_n + Z_{n+1})$ couples with $X'$: there is an almost surely finite random time $\tau$ with $X_n = X'_n$ for all $n > \tau$; consequently $d_{\mathrm{TV}}(\mathrm{Law}(X_n), \mathrm{Law}(X'_0)) \le P(\tau \ge n) \to 0$.

Proof. Started empty at time $-N$, the recursion gives at time $0$ the value $\max(0, V_1, \dots, V_N)$, which increases with $N$ to $X'_0$. By the ergodic theorem applied to the reversed sequence, $V_n/n \to E[Z_0] < 0$ almost surely, so $V_n \to -\infty$ and the supremum is attained, hence finite. Writing $X'_n = F(\theta^n Z)$ with $F(z) = \sup_{k \ge 0}(z_0 + \dots + z_{-k+1})$ and $\theta$ the left shift shows that $X'$ satisfies the recursion and is a stationary ergodic factor of $Z$. For any real initial value, unrolling the recursion gives $X_n = \max\big(0, Z_n, Z_n + Z_{n-1}, \dots, Z_n + \dots + Z_2, Z_n + \dots + Z_1 + X_0\big)$, the suffix sums of lengths $0, \dots, n-1$ together with $S_n + X_0$ where $S_n = Z_1 + \dots + Z_n$, and the same formula holds for $X'_n$ with $X'_0$ in place of $X_0$. By the ergodic theorem forward in time, $S_n \to -\infty$, so for large $n$ both last terms are negative and the two maxima agree. Since $X'$ is stationary, $\mathrm{Law}(X'_n) = \mathrm{Law}(X'_0)$, and $X_n \ne X'_n$ only on $\{\tau \ge n\}$.

## Proof depends on

- [Birkhoff pointwise ergodic theorem (ergodic case)](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/birkhoff-pointwise-ergodic.md): the ergodic theorem for the shift, forward and for the reversed sequence.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- A two-sided stationary ergodic sequence is the coordinate process of an invertible ergodic shift, and its time reversal is again stationary ergodic.
- If $X_n = X'_n$ for all $n > \tau$ with $\tau$ almost surely finite, then $d_{\mathrm{TV}}(\mathrm{Law}(X_n), \mathrm{Law}(X'_n)) \le P(\tau \ge n) \to 0$.

## Background

- [The supremum of the random walk is a stationary law of Lindley's recursion](stationary-law-of-the-lindley-recursion.md): the i.i.d. case.

## Sources

- L. Györfi and G. Morvai, "Queueing for ergodic arrivals and services", in *Limit Theorems in Probability and Statistics*, Vol. II, János Bolyai Mathematical Society, Budapest, 2002, pp. 127–141, author copy <http://math.bme.hu/~morvai/publications/papers/GyorfiMorvai2002ARX.pdf>, §2.1, Definition 1 and Theorem 1 with its proof (Steps 1–3), revisiting R. M. Loynes (1962); §2.3, Corollary 2 for waiting times
