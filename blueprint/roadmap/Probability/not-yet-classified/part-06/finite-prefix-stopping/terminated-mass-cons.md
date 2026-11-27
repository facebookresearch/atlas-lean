# One-step unfolding of terminated mass

Let $q$ assign to each prefix $p$ a next-symbol distribution $q(p)$ over the tokens and an end-of-string symbol EOS. For a finite string $w$, its terminated mass is the probability of emitting exactly the tokens of $w$ in order and then EOS. For a token $a$ and a string $w$,

$$\text{mass}_q(a w) = q(\varepsilon)(a)\cdot\text{mass}_{q_a}(w),$$

where $\varepsilon$ is the empty prefix and $q_a(p) = q(a p)$ is the distribution conditioned on the first token $a$.
