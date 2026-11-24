# Endowment insurance and the annuity-due identity

Let $T \ge 0$ be a measurable lifetime, $S_k = P(T > k)$ with $S_0 = 1$, $n \ge 0$ an integer and $v > 0$. The expected present values $A = E[\sum_{k<n} v^{k+1}\mathbf 1\{k < T \le k + 1\}] = \sum_{k<n} v^{k+1}(S_k - S_{k+1})$ of an $n$-year term insurance paid at the end of the year of death, $E[v^n\mathbf 1\{T > n\}] = v^nS_n$ of the survivor payment, and $\ddot a = E[\sum_{k<n} v^k\mathbf 1\{T > k\}] = \sum_{k<n} v^kS_k$ of an annuity-due satisfy $A + v^nS_n = 1 - (1 - v)\ddot a$, by summation by parts. The terminal survivor payment $v^nS_n$ cannot be dropped.

## Sources

- E. A. Valdez, *Annuities*, lecture slides, STT 455 Actuarial Models, Michigan State University, Fall 2014, n-year annuity-due slides, <https://users.math.msu.edu/users/valdezea/stt455f14/STT455Weeks9to11-F2014.pdf>
