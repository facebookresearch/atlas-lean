# Every experts algorithm has expected regret at least $\sqrt{T}/(2e)$ against fair coin losses

Let $X$ have $N \ge 2$ actions and $T \ge 0$. There is a family of binary loss sequences indexed by $w \in \{0,1\}^T$ (fair coin flips) such that every causal online algorithm $H$ has expected loss at least $T/2$ (exactly $T/2$ if it plays only the two coin actions below) and expected external regret

$$
\mathbb{E}_w\left[L_H^T(\ell^w) - L_{\min}^T(\ell^w)\right] \ge \frac{1}{2e}\sqrt{T}.
$$

## Proof sketch

Use two actions with complementary losses $w_t$ and $1 - w_t$ (others always lose $1$). The algorithm's expected loss is at least $1/2$ per round by causality, since each coin action loses with probability $1/2$ over the fresh bit. The best action has loss $T/2 - |S|/2$ with $S = \sum_t (2w_t - 1)$, so the expected regret is $\mathbb{E}|S|/2$, and Khintchine's $L^1$ lower bound $\mathbb{E}|S| \ge \sqrt{T}/e$ finishes.

## Depends on

- [Causal online algorithm in the experts setting](causal-online-experts-algorithm.md)

## Proof depends on

- [Khintchine inequality](../../../../Probability/concentration-inequalities/khintchine-inequality.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
