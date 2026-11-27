# Anytime regret of online gradient descent

Let $E$ be a real inner product space, $D > 0$, $G > 0$, $\Pi$ a 1-Lipschitz projection with $\Pi(x^*) = x^*$, and suppose $f_t(x) + \langle g_t(x), x^* - x\rangle \le f_t(x^*)$ for all $t$ and $x$. Run $x_{t+1} = \Pi(x_t - \eta_t\,g_t(x_t))$ from any $x_0$ with $\eta_t = D/(G\sqrt{t+1})$, and assume $\lVert x_t - x^*\rVert \le D$ and $\lVert g_t(x_t)\rVert \le G$ for all $t$. Then for every $T$,

$$\sum_{t<T} \bigl(f_t(x_t) - f_t(x^*)\bigr) \le \frac32\,G D \sqrt T.$$
