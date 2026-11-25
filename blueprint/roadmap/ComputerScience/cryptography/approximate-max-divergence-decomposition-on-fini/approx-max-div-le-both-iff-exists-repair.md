# Two-sided approximate max-divergence and simultaneous repair

Let $\Omega$ be a finite nonempty type and $P, Q$ probability mass functions on $\Omega$, and $\varepsilon \ge 0$, $\delta \ge 0$. Then both [approximate bounds](approx-max-div-le.md) $D_\infty^\delta(P \| Q) \le \varepsilon$ and $D_\infty^\delta(Q \| P) \le \varepsilon$ hold if and only if there are probability mass functions $P', Q'$ with

$$
\mathrm{TV}(P, P') \le \frac{\delta}{e^{\varepsilon} + 1}, \qquad \mathrm{TV}(Q, Q') \le \frac{\delta}{e^{\varepsilon} + 1},
$$

and the [pure bounds](max-div-le.md) $D_\infty(P' \| Q') \le \varepsilon$ and $D_\infty(Q' \| P') \le \varepsilon$, with $\mathrm{TV}(P, R) = \tfrac12 \sum_w |P(w) - R(w)|$ the total variation distance. The pure bound is required in both directions.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Lemma 3.17, part 2.
