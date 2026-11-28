# Greedy (follow-the-leader) loss bound with N experts

Let $X = \{1, \dots, N\}$ with $N \ge 1$ and let all losses be binary, $\ell_t \in \{0,1\}^X$. The Greedy algorithm plays action $1$ in the first round and in each later round the least-index action of minimum cumulative loss so far. For every loss sequence and every horizon $T$,

$$
L_{\mathrm{Greedy}}^T \le N \cdot L_{\min}^T + (N-1)
$$

(Blum and Mansour, Theorem 4.2).

## Proof sketch

Whenever Greedy incurs a loss of $1$ while $L_{\min}$ does not increase, at least one action leaves the set of current leaders, which can happen at most $N$ times before $L_{\min}$ increases by $1$; inductively $L_{\mathrm{Greedy}}^t \le N - |S^t| + N \cdot L_{\min}^t$, where $S^t$ is the leader set (proof of Theorem 4.2).

Derived (not stated in the cited source, which only remarks that the binary case can be easily extended): the same bound holds for arbitrary loss vectors $\ell_t \in [0,1]^X$ and any play $x_t$ that is a current leader, $\sum_{s<t} \ell_s(x_t) = \min_{i} \sum_{s<t} \ell_s(i)$, with ties broken arbitrarily. Track the potential $\Phi_t = \sum_i \max\{0, 1 + L_{\min}^t - \sum_{s<t}\ell_s(i)\}$, which lies in $[1, N]$; a round in which the played leader suffers loss $\lambda$ either decreases the potential by at least $\lambda$ or raises $L_{\min}$, and telescoping gives the bound.

## Depends on

- [Causal online algorithm in the experts setting](causal-online-experts-algorithm.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4, Section 4.3.1 and Theorem 4.2.
