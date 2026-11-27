# Greedy (follow-the-leader) loss bound with N experts

Let $X$ be a finite set of $N \ge 1$ actions and $\ell_0, \ell_1, \ldots \in [0,1]^X$ arbitrary loss vectors. Let $x_0, x_1, \ldots$ be any sequence of actions with $x_t$ a current leader, $\sum_{s<t} \ell_s(x_t) = \min_{i} \sum_{s<t} \ell_s(i)$, for every $t < T$ (ties broken arbitrarily). Then

$$
\sum_{t<T} \ell_t(x_t) \le N \cdot L_{\min}^T + (N-1).
$$

## Proof sketch

Track the potential $\Phi_t = \sum_i \max\{0, 1 + L_{\min}^t - \sum_{s<t}\ell_s(i)\}$, which lies in $[1, N]$ and counts (fractionally) the actions within one unit of the leader. A round in which the played leader suffers loss $\lambda$ either decreases the potential by at least $\lambda$ or raises $L_{\min}$; the minimum can grow by at most one unit per full depletion of the potential. Telescoping over $T$ rounds gives the bound, which extends the source's $\{0,1\}$ argument to $[0,1]$ losses.

## Depends on

- [Causal online algorithm in the experts setting](causal-online-experts-algorithm.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
