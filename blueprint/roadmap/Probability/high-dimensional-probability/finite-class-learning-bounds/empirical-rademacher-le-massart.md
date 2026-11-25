# Massart's finite-class lemma

For a finite set $A \subseteq \mathbb{R}^n$, let $\hat{\mathfrak R}(A) = 2^{-n}\sum_{\sigma \in \{\pm1\}^n}\max_{a \in A}\frac1n\sum_i\sigma_ia_i$ be its empirical Rademacher complexity (one-sided, $0$ for $A = \emptyset$). For nonempty $A$,

$$\hat{\mathfrak R}(A) \le \frac{\max_{a \in A}\|a\|_2\,\sqrt{2\log|A|}}{n}.$$

At $n = 0$ both sides are $0$.
