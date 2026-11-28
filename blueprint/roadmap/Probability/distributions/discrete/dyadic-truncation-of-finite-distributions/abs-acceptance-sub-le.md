# Abs acceptance sub le

Let $L$ be a finite set with $K$ elements and $\pi : L \to \mathbb{R}$ a probability vector, $\pi_l \ge 0$ for all $l$ and $\sum_l \pi_l = 1$. For $t \in \mathbb{N}$ let $q_l = \lfloor 2^t \pi_l \rfloor / 2^t$ be the dyadic truncation at precision $t$, and let $a : L \to [0, 1]$ be acceptance probabilities. Then

$$\Big\lvert \sum_{l \in L} \pi_l a_l - \sum_{l \in L} q_l a_l \Big\rvert \le \frac{2K}{2^t}.$$

The reject outcome, which accepts with probability $0$, contributes no term.
