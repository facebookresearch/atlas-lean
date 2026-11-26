# Deterministic experts algorithms suffer loss T while the best expert has floor(T/N)

Let $X$ have $N \ge 1$ actions and let $D$ be any deterministic online algorithm in the experts setting (its action in round $t$ depends only on the losses of earlier rounds). For every horizon $T$ there is a binary loss sequence $\ell_t \in \{0,1\}^X$ on which $D$ suffers total loss exactly $T$ while $L_{\min}^T = \lfloor T/N \rfloor$. Hence no deterministic algorithm has external regret below $T - \lfloor T/N \rfloor$ in the worst case.

## Proof sketch

The adversary gives loss $1$ to the action $D$ is about to play and $0$ to every other action; it can do so because the action is determined by the past. The algorithm loses $1$ per round, the total loss $T$ is spread over $N$ actions, and choosing the order carefully makes the least-loaded action receive exactly $\lfloor T/N \rfloor$.

## Depends on

- [Causal online algorithm in the experts setting](causal-online-experts-algorithm.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
