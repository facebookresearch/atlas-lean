# Deductible, limit and coinsurance as a capped call spread

Let $S \ge 0$ be an aggregate loss, $d \ge 0$ a deductible, $L > 0$ a limit and $\rho \in [0, 1]$ a coinsurance share. The ceded loss of the layer is

$$X = \rho \min\bigl((S - d)^+, L\bigr) = \rho\bigl((S - d)^+ - (S - d - L)^+\bigr),$$

a long call at $d$ and a short call at $d + L$ on the loss, scaled by $\rho$, and the retained loss is $S - X$. Then $0 \le X \le \min(S, \rho L)$, so the retained loss is nonnegative and retained plus ceded equals $S$. If $S$ is integrable, $\mathbb E X = \rho\bigl(\pi(d) - \pi(d + L)\bigr)$ with the stop-loss transform $\pi(t) = \mathbb E (S - t)^+$.

## Sources

- R. Kaas, M. Goovaerts, J. Dhaene and M. Denuit, *Modern Actuarial Risk Theory*, 2nd ed., Springer, 2008, Chapter 1 (reinsurance and stop-loss premiums)
