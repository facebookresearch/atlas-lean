# Dyadic Trunc

Let $L$ be a set, $\pi : L \to \mathbb{R}$ and $t \in \mathbb{N}$. The dyadic truncation of $\pi$ at precision $t$ is the function $q : L \to \mathbb{R}$ given by

$$q_l = \frac{\lfloor 2^t \pi_l \rfloor_+}{2^t},$$

where $\lfloor x \rfloor_+$ is the natural-number floor, equal to $\lfloor x \rfloor$ for $x \ge 0$ and to $0$ for $x < 0$. Thus, for $\pi_l \ge 0$, $q_l$ rounds $\pi_l$ down to a multiple of $2^{-t}$; and $q_l = 0$ whenever $\pi_l < 2^{-t}$.
