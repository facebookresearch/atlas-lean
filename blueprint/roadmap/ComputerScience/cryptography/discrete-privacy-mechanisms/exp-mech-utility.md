# Utility of the exponential mechanism

Let $R$ be finite and nonempty, $\varepsilon > 0$ and $\Delta > 0$. For every database $d$ and every real $t$, the [exponential mechanism](exp-mech.md) at $d$ satisfies

$$
\Pr\Big[u(d, r) \le \mathrm{OPT}(u(d, \cdot)) - \frac{2\Delta}{\varepsilon}\big(\log |R| + t\big)\Big] \le e^{-t},
$$

where $\mathrm{OPT}$ is the [optimal utility](../laplace-and-exponential-mechanisms/opt-utility.md).

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Corollary 3.12.
