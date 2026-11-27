# Distribution of the exclusive or of independent bits

Let $p_0, \dots, p_{n-1}$ be distributions on bits, and draw a word $w \in \{\mathrm{false}, \mathrm{true}\}^n$ with independent letters $w_i \sim p_i$. The probability that the exclusive or $w_0 \oplus \cdots \oplus w_{n-1}$ equals $b$ is

$$\sum_{w \,:\, w_0 \oplus \cdots \oplus w_{n-1} = b}\ \prod_{i < n} p_i(w_i).$$
