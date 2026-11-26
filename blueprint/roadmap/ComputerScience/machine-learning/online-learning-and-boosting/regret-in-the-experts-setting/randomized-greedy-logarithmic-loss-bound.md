# Randomized greedy loss bound $\ln N + (1 + \ln N) L_{\min}$

Let $X$ be a finite set of $N \ge 1$ actions and let all losses be binary, $\ell_t \in \{0,1\}^X$. Randomized greedy plays in round $t$ the uniform distribution on the leader set $S^t$. Its expected loss over any horizon $T$ satisfies

$$
L_{RG}^T \le \ln N + (1 + \ln N)\, L_{\min}^T .
$$

More precisely $L_{RG}^T \le (H_N - H_{|S^T|}) + H_N L_{\min}^T$, where $H_k = \sum_{j \le k} 1/j$. The restriction to binary losses is needed: arbitrarily small real perturbations can keep a unique leader in every round.

## Proof sketch

Between two consecutive increases of $L_{\min}$, each round in which $j$ of the current $k$ leaders suffer loss costs the algorithm $j/k \le H_k - H_{k-j}$, and those $j$ leaders leave the leader set. Summing within an epoch gives at most $H_N$, and in the final partial epoch at most $H_N - H_{|S^T|}$. There are $L_{\min}^T$ completed epochs, and $H_N \le 1 + \ln N$.

## Depends on

- [Causal online algorithm in the experts setting](causal-online-experts-algorithm.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
