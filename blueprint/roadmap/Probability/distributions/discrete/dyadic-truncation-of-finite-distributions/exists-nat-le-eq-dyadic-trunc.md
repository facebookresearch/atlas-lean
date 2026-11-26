# Exists nat le eq dyadic Trunc

Let $L$ be a set, $\pi : L \to \mathbb{R}$ with $\pi_l \le 1$ for all $l$, $t \in \mathbb{N}$ and $l \in L$, and let $q_l = \lfloor 2^t \pi_l \rfloor_+ / 2^t$ be the dyadic truncation of $\pi$ at precision $t$ (with $\lfloor x \rfloor_+ = 0$ for $x < 0$). Then there is $n \in \mathbb{N}$ with

$$n \le 2^t \quad \text{and} \quad q_l = \frac{n}{2^t},$$

so $q_l$ is the probability of an event determined by $t$ fair coin flips.
