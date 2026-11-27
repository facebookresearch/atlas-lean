# Prefix Prod

Let $T$ be a finite alphabet and let $q$ assign to every finite word $w \in T^*$ a probability distribution $q(w)$ on $T$. The prefix product of a word is the extended nonnegative real defined by recursion on the word:

$$\Pi_q(\varepsilon) = 1, \qquad \Pi_q(a w) = q(\varepsilon)(a) \cdot \Pi_{q_a}(w),$$

where $\varepsilon$ is the empty word and $q_a(u) = q(a u)$ is the kernel shifted by $a$. Unfolding, for $w = a_1 a_2 \cdots a_k$,

$$\Pi_q(w) = \prod_{j=1}^{k} q(a_1 \cdots a_{j-1})(a_j).$$
