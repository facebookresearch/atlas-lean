# Causal online algorithm in the experts setting

Fix a finite nonempty set $X$ of $N$ actions (experts). An adversary chooses loss vectors $\ell_0, \ell_1, \ldots \in [0,1]^X$. A (randomized) online algorithm $H$ assigns to every round $t$ and every loss history a probability distribution $p_t = H(\ell_0, \ldots, \ell_{t-1}) \in \Delta(X)$ that depends only on the losses of rounds before $t$. A deterministic online algorithm instead outputs an action $x_t \in X$ determined by $\ell_0, \ldots, \ell_{t-1}$.

Over a horizon $T$ the expected loss of $H$ is $L_H^T = \sum_{t<T} \sum_{i \in X} p_t(i)\,\ell_t(i)$, the best fixed action has loss $L_{\min}^T = \min_{i \in X} \sum_{t<T} \ell_t(i)$, and the external regret is $L_H^T - L_{\min}^T$. The set of leaders before round $t$ is $S^{t} = \{ i : \sum_{s<t} \ell_s(i) = L_{\min}^t \}$.

## Depends on

- [External regret](../../../../GameTheory/noncooperative-games/external-and-swap-regret/external-regret.md)
- [Cumulative loss](../../../../GameTheory/noncooperative-games/external-and-swap-regret/cumulative-loss.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
