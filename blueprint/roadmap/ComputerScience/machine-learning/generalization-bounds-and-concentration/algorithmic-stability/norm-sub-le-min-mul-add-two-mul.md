# Growth recursion for two bounded updates

Let $G$ and $G'$ be maps of a normed space into itself. Suppose $G$ is $\eta$-expansive, $\lVert G(v) - G(w)\rVert \le \eta \lVert v - w\rVert$, and that both are $\sigma$-bounded, $\lVert w - G(w)\rVert \le \sigma$ and $\lVert w - G'(w)\rVert \le \sigma$ for all $w$. Then for all $v, w$,

$$
\lVert G(v) - G'(w) \rVert \le \min(\eta, 1)\, \lVert v - w \rVert + 2\sigma .
$$

Proof: $G(v) - G'(w) = (v - w) - (v - G(v)) + (w - G'(w))$ gives the bound with $1$, and $G(v) - G'(w) = (G(v) - G(w)) - (w - G(w)) + (w - G'(w))$ gives the bound with $\eta$.

Along two runs $w_{t+1} = G_t(w_t)$, $w'_{t+1} = G'_t(w'_t)$ from the same start, the distance $\delta_t = \lVert w_t - w'_t\rVert$ thus satisfies $\delta_{t+1} \le \eta\, \delta_t$ when $G_t = G'_t$, and $\delta_{t+1} \le \min(\eta, 1)\,\delta_t + 2\sigma$ otherwise. This recursion is the engine of [the stability of SGM](integral-abs-sgm-output-sub-le.md).

## Sources

- M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Lemma 2.5 (second case; the first case is the definition of expansiveness), with Definitions 2.3 and 2.4 ($\eta$-expansive and $\sigma$-bounded update rules).
