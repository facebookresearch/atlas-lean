# Randomized greedy loss bound $\ln N + (1 + \ln N) L_{\min}$

Let $X$ be a finite set of $N \ge 1$ actions and let all losses be binary, $\ell_t \in \{0,1\}^X$. Randomized greedy plays in round $t$ the uniform distribution on the leader set $S^t$. Its expected loss over any horizon $T$ satisfies

$$
L_{RG}^T \le \ln N + (1 + \ln N)\, L_{\min}^T
$$

(Blum and Mansour, Theorem 4.4).

## Proof sketch

Between two consecutive increases of $L_{\min}$, each round in which the leader set shrinks by $j$ from size $k$ to $k - j$ costs the algorithm $j/k \le 1/k + 1/(k-1) + \dots + 1/(k-j+1)$, so the loss between successive increases of $L_{\min}$ is at most $1/N + 1/(N-1) + \dots + 1 \le 1 + \ln N$; inductively $L_{RG}^t \le (1/N + 1/(N-1) + \dots + 1/(|S^t| + 1)) + (1 + \ln N) L_{\min}^t$ (proof of Theorem 4.4).

Derived (not stated in the cited source): the same argument with $H_k = \sum_{j \le k} 1/j$ in place of $1 + \ln N$ gives $L_{RG}^T \le (H_N - H_{|S^T|}) + H_N L_{\min}^T$.

## Depends on

- [Causal online algorithm in the experts setting](causal-online-experts-algorithm.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4, Section 4.3.1 and Theorem 4.4.
