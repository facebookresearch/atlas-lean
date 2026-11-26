# Law

Let $T$ be a finite alphabet and let $q$ assign to every finite word $w \in T^*$ a probability distribution $q(w)$ on $T$, the next-token law after prefix $w$. The horizon-$n$ word law $\mathcal{L}_n(q)$ is the probability distribution on $T^*$ defined by recursion on $n$:

- $\mathcal{L}_0(q)$ is the point mass at the empty word;
- $\mathcal{L}_{n+1}(q)$ draws a head token $a \sim q(\varepsilon)$, where $\varepsilon$ is the empty word, then a tail $w \sim \mathcal{L}_n(q_a)$ for the shifted kernel $q_a(u) = q(a u)$, and returns the word $a w$.

Equivalently, $\mathcal{L}_{n+1}(q)(v) = \sum_{a \in T} q(\varepsilon)(a) \, \mathcal{L}_n(q_a)(\{ w : a w = v \})$.
