# Utility of the exponential mechanism, simple form

Fix a database $x$, $\varepsilon > 0$ and $\Delta > 0$. For every $t$,

$$
\Pr\Big[u(x, M_E(x)) \le \mathrm{OPT}_u(x) - \frac{2\Delta}{\varepsilon}(\ln |R| + t)\Big] \le e^{-t},
$$

since $|R_{\mathrm{OPT}}| \ge 1$ (the bound is trivial for $t < 0$).

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Corollary 3.12.
