# Pointwise AIPW score error

Let $T \subseteq \mathcal{W}$, let $Y, Y_0, Y_1, e, g_0, g_1, e^\circ, \mu_0, \mu_1 : \mathcal{W} \to \mathbb{R}$, and let $\psi(e, g_0, g_1) = g_1 - g_0 + \mathbf{1}_T (Y - g_1)/e - \mathbf{1}_{T^c} (Y - g_0)/(1 - e)$ be the AIPW score. Fix a point $w$ and $\varepsilon, \varepsilon_0 > 0$, and suppose

- $Y(w) = Y_1(w)$ if $w \in T$ and $Y(w) = Y_0(w)$ if $w \notin T$;
- $\varepsilon \le e(w) \le 1 - \varepsilon$;
- $\varepsilon_0 \le e^\circ(w) \le 1 - \varepsilon_0$.

Then, with every function evaluated at $w$,

$$\bigl\lvert \psi(e, g_0, g_1) - \psi(e^\circ, \mu_0, \mu_1) \bigr\rvert \le (1 + \varepsilon^{-1})\bigl(\lvert \mu_1 - g_1 \rvert + \lvert \mu_0 - g_0 \rvert\bigr) + \varepsilon^{-1} \varepsilon_0^{-1} \bigl(\lvert Y_1 - \mu_1 \rvert + \lvert Y_0 - \mu_0 \rvert\bigr) \lvert e^\circ - e \rvert.$$
