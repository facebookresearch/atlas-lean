# Shapiro's question on inverses in the analytic Wiener algebra

Hayman–Lingham Problem 5.42 (H. S. Shapiro), answered in Nikolski's normalization. Call $\delta > 0$ admissible when there exists one constant $M$ that [bounds the inverse coefficients at level $\delta$](inverse-bounded-by.md) for every eligible function at once: for every $f(z) = \sum a_n z^n$ with $\sum |a_n| \le 1$ and $|f(z)| \ge \delta$ throughout the open unit disc, the Taylor coefficients $b_n$ of $1/f$ (determined by $\sum b_n z^n = 1/f(z)$ on the disc) satisfy $\sum_{n < N} |b_n| \le M$ for every $N$. The statement is that the infimum of the admissible $\delta$ is $1/2$.

The order of quantifiers matters: $M$ depends on $\delta$ only, not on $f$. For a single $f$ with $|f| \ge \delta > 0$ on the disc, $1/f$ always has absolutely summable coefficients by Wiener's lemma, so allowing $M$ to depend on $f$ would change the question.

Its resolution: [Nikolski's critical constant 1/2 for the analytic Wiener algebra](critical-delta-is-one-half-holds.md).
