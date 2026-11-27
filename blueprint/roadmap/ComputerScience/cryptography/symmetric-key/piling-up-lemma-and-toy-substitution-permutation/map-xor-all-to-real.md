# Map xor All to Real

Throughout, $n \in \mathbb{N}$, $p_0, \dots, p_{n-1}$ are probability distributions on $\{\mathrm{false}, \mathrm{true}\}$, and $w$ ranges over the finite set $\mathrm{Bool}^n$ of words $w = (w_0, \dots, w_{n-1})$. Let $X(w) = w_0 \oplus \cdots \oplus w_{n-1}$ be the [XOR of all bits](../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/yao-s-xor-lemma/xor-fold.md) of $w$ (false for $n = 0$), and $W(w) = \prod_{i<n} \mathrm{toReal}(p_i(w_i))$. For each $b \in \mathrm{Bool}$, the real-converted mass at $b$ of the pushforward of the [product joint distribution](joint-pmf.md) under $X$ is the sum of $W$ over the fiber of $b$:

$$
\mathrm{toReal}\Bigl(\Pr_{w \sim \mathrm{joint}}[X(w) = b]\Bigr) = \sum_{w \in \mathrm{Bool}^n,\ X(w) = b} W(w).
$$
