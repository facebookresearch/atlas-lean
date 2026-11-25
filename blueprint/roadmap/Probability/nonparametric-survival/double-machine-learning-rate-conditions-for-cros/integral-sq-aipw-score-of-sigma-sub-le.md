# The `L²` error of the AIPW score is bounded by the `L²` nuisance errors

Let $\nu$ be a probability measure on a measurable space $\mathcal{W}$, $m$ a sub-σ-algebra (the covariate information), $T \subseteq \mathcal{W}$ and $Y, Y_0, Y_1 : \mathcal{W} \to \mathbb{R}$. Write $e^* = \nu[\mathbf{1}_T \mid m]$, $\mu_a^* = \nu[Y_a \mid m]$, $\lVert f \rVert_2^2 = \int f^2 \, d\nu$, and let $\psi(e, g_0, g_1) = g_1 - g_0 + \mathbf{1}_T (Y - g_1)/e - \mathbf{1}_{T^c} (Y - g_0)/(1 - e)$ be the AIPW score. Assume

- consistency: $Y = \mathbf{1}_T Y_1 + \mathbf{1}_{T^c} Y_0$ $\nu$-a.e.;
- $Y_0, Y_1 \in L^2(\nu)$;
- strong overlap: $\varepsilon_0 \le e^* \le 1 - \varepsilon_0$ $\nu$-a.e. for some $\varepsilon_0 > 0$;
- bounded conditional variances: $\nu[(Y_a - \mu_a^*)^2 \mid m] \le C$ $\nu$-a.e. for $a = 0, 1$.

Let $e$ be strongly $m$-measurable with $\varepsilon \le e \le 1 - \varepsilon$ $\nu$-a.e. for some $\varepsilon > 0$, and let $g_0, g_1 \in L^2(\nu)$. Then

$$\bigl\lVert \psi(e, g_0, g_1) - \psi(e^*, \mu_0^*, \mu_1^*) \bigr\rVert_2^2 \le 4 (1 + \varepsilon^{-1})^2 \bigl(\lVert \mu_1^* - g_1 \rVert_2^2 + \lVert \mu_0^* - g_0 \rVert_2^2\bigr) + 8 C (\varepsilon^{-1} \varepsilon_0^{-1})^2 \lVert e^* - e \rVert_2^2.$$
