# Rademacher complexity of a class of binary vectors

For a finite set $A \subseteq \mathbb{R}^n$, let $\hat{\mathfrak R}(A) = 2^{-n}\sum_{\sigma \in \{\pm1\}^n}\max_{a \in A}\frac1n\sum_i\sigma_ia_i$ be its empirical Rademacher complexity (one-sided, $0$ for $A = \emptyset$). For a nonempty finite set $H \subseteq \{0, 1\}^m$ and its image $\tilde H \subseteq \{\pm1\}^m$ under $h \mapsto (2h_i - 1)_i$, $\hat{\mathfrak R}(\tilde H) = \frac1m\cdot2^{-m}\sum_\sigma\max_{h \in H}\sum_i\sigma_i(2h_i - 1)$.
