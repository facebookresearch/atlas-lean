# Law succ

Let $T$ be a finite alphabet and let $q$ assign to every finite word $w$ a probability distribution $q(w)$ on $T$; write $\varepsilon$ for the empty word and $q_a(u) = q(a u)$ for the kernel shifted by $a \in T$. For every $n \in \mathbb{N}$, the horizon-$(n+1)$ word law is obtained by drawing $a \sim q(\varepsilon)$, then $w \sim \mathcal{L}_n(q_a)$, and returning $a w$:

$$\mathcal{L}_{n+1}(q)(v) = \sum_{a \in T} q(\varepsilon)(a) \, \mathcal{L}_n(q_a)\big(\{ w : a w = v \}\big) \quad \text{for every word } v.$$
