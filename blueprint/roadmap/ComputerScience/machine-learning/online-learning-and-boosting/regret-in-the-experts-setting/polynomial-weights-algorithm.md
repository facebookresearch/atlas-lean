# Multiplicative weights (polynomial weights) algorithm

Let $X$ be a finite set of $n$ experts and $\eta > 0$ a learning rate. The multiplicative weights algorithm (also called polynomial weights, or the prod algorithm) keeps weights $w_0(i) = 1$ and updates $w_{t+1}(i) = w_t(i)\,(1 - \eta\,\ell_t(i))$ after observing the loss vector $\ell_t$. In round $t$ it plays $p_t(i) = w_t(i) / \sum_j w_t(j)$. On binary losses this coincides with randomized weighted majority with penalty factor $1-\eta$; replacing the factor $1 - \eta x$ by $e^{-\eta x}$ gives Hedge.

## Depends on

- [Causal online algorithm in the experts setting](causal-online-experts-algorithm.md)

## Sources

- Sanjeev Arora, Elad Hazan and Satyen Kale, "The Multiplicative Weights Update Method: a Meta-Algorithm and Applications", Theory of Computing 8, 2012.
- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
