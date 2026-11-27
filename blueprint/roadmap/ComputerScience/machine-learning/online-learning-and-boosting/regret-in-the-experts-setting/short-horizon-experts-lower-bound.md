# Short-horizon lower bound: expected loss T/2 with a perfect expert when 2^T <= N

Let $X$ have $N$ actions and $T$ a horizon with $2^T \le N$. There is a family of binary loss sequences $(\ell^w)_{w \in \{0,1\}^T}$ such that for every $w$ some action has zero total loss ($L_{\min}^T(\ell^w) = 0$), while every causal online algorithm $H$ satisfies

$$
\mathbb{E}_{w}\, L_H^T(\ell^w) = T/2
$$

for $w$ uniform on $\{0,1\}^T$. In particular, for $T < \log_2 N$, every algorithm has expected regret $T/2$.

## Proof sketch

Since $2^T \le N$, choose a surjective labelling of the actions by strings $b \in \{0,1\}^T$ and, in round $t$, give an action labelled $b$ the loss $1$ exactly when $b_t \ne w_t$. Some action is labelled $w$ and never loses. Since $p_t$ depends only on $w_0, \ldots, w_{t-1}$, every action loses with probability $1/2$ over the fresh bit $w_t$, giving expected loss $1/2$ per round.

## Depends on

- [Causal online algorithm in the experts setting](causal-online-experts-algorithm.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
