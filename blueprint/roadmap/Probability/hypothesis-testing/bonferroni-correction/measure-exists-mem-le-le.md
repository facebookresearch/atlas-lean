# Union bound for valid p-values

Let $\mu$ be a measure on $\Omega$, $p_0, \dots, p_{m-1} : \Omega \to \mathbb{R}$ and $H_0 \subseteq \{0, \dots, m-1\}$ such that each $p_i$, $i \in H_0$, is a valid p-value under $\mu$ ($\mu(p_i \le t) \le t$ for all $t \in [0,1]$). For every $c \in [0,1]$,

$$\mu(\exists i \in H_0 : p_i \le c) \le |H_0|\, c.$$

No independence is assumed.
