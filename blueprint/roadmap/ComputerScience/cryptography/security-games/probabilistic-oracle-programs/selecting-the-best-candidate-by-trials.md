# Selecting the best candidate by repeated trials

Let $c_0, \dots, c_{m-1}$ be candidates, each with an unknown acceptance probability $p_i$ of a probabilistic test. The selection procedure runs the test $t$ times on each candidate, computes empirical frequencies $\hat p_i$, and returns a candidate with maximal success count. If each estimate satisfies $|\hat p_i - p_i| \le \varepsilon$ except with probability $\eta$ (by Hoeffding, $\eta \le 2e^{-2t\varepsilon^2}$), then the selected candidate $c_{\hat \imath}$ satisfies

$$p_{\hat\imath} \ge \max_i p_i - 2\varepsilon$$

except with probability at most $m\eta$. No independence between the estimates of different candidates is needed for the selection step itself.

## Proof sketch

On the event that all $m$ estimates are $\varepsilon$-accurate (union bound over candidates), the empirical maximizer's true value is at least its estimate minus $\varepsilon$, which is at least the best candidate's estimate minus $\varepsilon$, hence at least the best value minus $2\varepsilon$.

## Depends on

- [Hoeffding's inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
- R. Impagliazzo, "Hard-Core Distributions for Somewhat Hard Problems", Proceedings of the 36th Annual IEEE Symposium on Foundations of Computer Science (FOCS), 1995.
