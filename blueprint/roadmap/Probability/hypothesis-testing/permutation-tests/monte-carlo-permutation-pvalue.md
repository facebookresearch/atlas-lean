# Monte Carlo permutation p-value

Let a group $G$ act on a set $\Omega$, $T : \Omega \to \mathbb{R}$ a statistic, $B \in \mathbb{N}$, $\omega \in \Omega$ and $g_1, \dots, g_B \in G$. The Monte Carlo permutation p-value is

$$\hat p_T(\omega; g_1, \dots, g_B) = \frac{1 + \#\{b : T(g_b \cdot \omega) \ge T(\omega)\}}{B + 1}.$$
