# Sharp utility bound for the exponential mechanism

Let $R$ be finite and nonempty, $\varepsilon > 0$ and $\Delta > 0$. For a database $d$ let $R_{\mathrm{OPT}} = \{ r \mid u(d, r) = \mathrm{OPT}(u(d, \cdot)) \}$ be the set of outputs attaining the [optimal utility](../laplace-and-exponential-mechanisms/opt-utility.md). For every real $t$, the [exponential mechanism](exp-mech.md) at $d$ satisfies

$$
\Pr\Big[u(d, r) \le \mathrm{OPT}(u(d, \cdot)) - \frac{2\Delta}{\varepsilon}\Big(\log \frac{|R|}{|R_{\mathrm{OPT}}|} + t\Big)\Big] \le e^{-t}.
$$

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Theorem 3.11.
