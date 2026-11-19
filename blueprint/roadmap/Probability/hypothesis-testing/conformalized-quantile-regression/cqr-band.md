# CQR prediction band

Let $\mathcal{X}$ be a set, $q_{\mathrm{lo}}, q_{\mathrm{hi}} : \mathcal{X} \to \mathbb{R}$ and $Q \in \mathbb{R} \cup \{+\infty\}$ a threshold. The CQR band at $x \in \mathcal{X}$ is

$$C_Q(x) = \{y \in \mathbb{R} : q_{\mathrm{lo}}(x) - y \le Q \text{ and } y - q_{\mathrm{hi}}(x) \le Q\},$$

the interval $[q_{\mathrm{lo}}(x) - Q, q_{\mathrm{hi}}(x) + Q]$ for real $Q$ (empty if $q_{\mathrm{lo}}(x) - Q > q_{\mathrm{hi}}(x) + Q$), and all of $\mathbb{R}$ when $Q = +\infty$.

## Sources

- Y. Romano, E. Patterson and E. J. Candès, *Conformalized quantile regression*, NeurIPS 2019, arXiv:1905.03222, Algorithm 1 (output).
