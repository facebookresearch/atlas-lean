# Data-processing inequality for entropy under a two-point mixture

Let $E$ be a finite set and $\mu$ a product probability weight on $\{0, 1\}^E$ whose coordinate weights $\mu_e(b)$ are all [strictly positive](esd-pos-weight.md); write $\mathbb{E}$ for the expectation under $\mu$ and $\Phi(x) = x \log x$ (with $\Phi(0) = 0$). Let $0 < p < 1$ and let $g_0, g_1 : \{0, 1\}^E \to [0, \infty)$. Then

$$p\, \Phi(\mathbb{E} g_1) + (1-p)\, \Phi(\mathbb{E} g_0) - \Phi\big(p\, \mathbb{E} g_1 + (1-p)\, \mathbb{E} g_0\big) \le \mathbb{E}\big[p\, \Phi(g_1) + (1-p)\, \Phi(g_0) - \Phi(p\, g_1 + (1-p)\, g_0)\big].$$
