# Each nuisance at rate `o_P(n^{-1/4})` suffices

Let $(\Omega, P)$ be a probability space, $\mathcal{W}$ a measurable space with a probability measure $\nu$, and $W_0, W_1, \dots : \Omega \to \mathcal{W}$ measurable, mutually independent and identically distributed with law $\nu$. Let $m$ be a sub-σ-algebra of the σ-algebra of $\mathcal{W}$ (the covariate information), $T \subseteq \mathcal{W}$ a measurable treatment event, $Y : \mathcal{W} \to \mathbb{R}$ measurable and $Y_0, Y_1 \in L^2(\nu)$. Write $e^* = \nu[\mathbf{1}_T \mid m]$, $\mu_a^* = \nu[Y_a \mid m]$, and let $\psi(e, g_0, g_1) = g_1 - g_0 + \mathbf{1}_T (Y - g_1)/e - \mathbf{1}_{T^c} (Y - g_0)/(1 - e)$ be the AIPW score, with oracle score $\psi^* = \psi(e^*, \mu_0^*, \mu_1^*)$. Let $K \in \mathbb{N}$ and let $\mathrm{fold} : \mathbb{N} \to \mathbb{N} \to \{0, \dots, K-1\}$ be a fold assignment, $\mathrm{fold}(n, i)$ being the fold of unit $i$ at sample size $n$. Write $U_{n,k}$ for the training data $(W_i)_{i < n,\ \mathrm{fold}(n,i) \ne k}$ of fold $k$, and $\lVert f \rVert_2 = (\int f^2 \, d\nu)^{1/2}$. For each $n$, fold $k$ and training value $u$, let $\hat e_{n,k}(u), \hat g_{0,n,k}(u), \hat g_{1,n,k}(u) : \mathcal{W} \to \mathbb{R}$ be fitted nuisances. Assume:

- consistency $Y = \mathbf{1}_T Y_1 + \mathbf{1}_{T^c} Y_0$ $\nu$-a.e.;
- mean exchangeability: $\nu[\mathbf{1}_T Y_1 \mid m] = e^* \mu_1^*$ and $\nu[\mathbf{1}_{T^c} Y_0 \mid m] = (1 - e^*) \mu_0^*$ $\nu$-a.e.;
- strong overlap: for some $\varepsilon_0 > 0$, $\varepsilon_0 \le e^* \le 1 - \varepsilon_0$ $\nu$-a.e.;
- the fitted nuisances are jointly measurable in $(u, w)$, strongly $m$-measurable in $w$ for each $u$, $\hat g_{a,n,k}(u) \in L^2(\nu)$, and for a fixed $\varepsilon > 0$, $\varepsilon \le \hat e_{n,k}(u)(w) \le 1 - \varepsilon$ for all $n, k, u, w$;
- bounded conditional variances: for some $C$, $\nu[(Y_a - \mu_a^*)^2 \mid m] \le C$ $\nu$-a.e. for $a = 0, 1$;
- for every fold $k$, each nuisance converges faster than $n^{-1/4}$ in $L^2$: $\sqrt{n}\, \lVert e^* - \hat e_{n,k}(U_{n,k}) \rVert_2^2 \xrightarrow{P} 0$, $\sqrt{n}\, \lVert \mu_0^* - \hat g_{0,n,k}(U_{n,k}) \rVert_2^2 \xrightarrow{P} 0$ and $\sqrt{n}\, \lVert \mu_1^* - \hat g_{1,n,k}(U_{n,k}) \rVert_2^2 \xrightarrow{P} 0$.

Let $\hat\tau_n = n^{-1} \sum_{i < n} \psi\bigl(\hat e_{n,k_i}(U_{n,k_i}), \hat g_{0,n,k_i}(U_{n,k_i}), \hat g_{1,n,k_i}(U_{n,k_i})\bigr)(W_i)$, with $k_i = \mathrm{fold}(n, i)$, be the cross-fitted AIPW estimator.

Then

$$\sqrt{n}\,\bigl(\hat\tau_n - \mathbb{E}_\nu[Y_1 - Y_0]\bigr) \xrightarrow{d} \mathcal{N}\bigl(0, \operatorname{Var}_\nu(\psi^*)\bigr),$$

that is, it converges in distribution to any random variable $Z$ on a probability space with $Z \sim \mathcal{N}(0, \operatorname{Var}_\nu(\psi^*))$. Consistency of each nuisance and the product rate both follow from these quarter rates.
