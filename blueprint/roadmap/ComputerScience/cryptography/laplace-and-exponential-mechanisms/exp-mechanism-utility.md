# Utility of the exponential mechanism

Fix a database $x$, $\varepsilon > 0$ and $\Delta > 0$, and let $R_{\mathrm{OPT}}$ be the set of
outputs attaining $\mathrm{OPT}_u(x)$. For every $t$,

$$
\Pr\Big[u(x, M_E(x)) \le \mathrm{OPT}_u(x) - \frac{2\Delta}{\varepsilon}\Big(\ln \frac{|R|}{|R_{\mathrm{OPT}}|} + t\Big)\Big] \le e^{-t}.
$$

The outputs below a level $c$ carry total weight at most $|R| e^{\varepsilon c / (2\Delta)}$, while the
normalising sum is at least $|R_{\mathrm{OPT}}| e^{\varepsilon \mathrm{OPT}_u(x) / (2\Delta)}$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Theorem 3.11 and its proof.
