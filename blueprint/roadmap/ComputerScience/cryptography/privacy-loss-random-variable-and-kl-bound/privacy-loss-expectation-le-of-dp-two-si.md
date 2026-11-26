# Upper bound on the expected privacy loss

Let $P, Q$ be probability mass functions on a type $\Omega$ and $\varepsilon \ge 0$, and assume the two-sided pointwise bounds $P(w) \le e^{\varepsilon} Q(w)$ and $Q(w) \le e^{\varepsilon} P(w)$ for every $w$. Then the [expected privacy loss](privacy-loss-expectation.md) satisfies

$$
\sum_w P(w)\, L_{P\|Q}(w) \le \varepsilon\,(e^{\varepsilon} - 1).
$$

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Lemma 3.18 (discrete case).
