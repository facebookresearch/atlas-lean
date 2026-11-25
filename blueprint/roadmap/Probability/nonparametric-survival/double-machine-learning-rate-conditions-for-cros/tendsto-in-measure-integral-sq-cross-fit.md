# Nuisance consistency gives score consistency

Let $P$ be a measure on $\Omega$, $\nu$ a probability measure on a measurable space $\mathcal{W}$, $m$ a sub-σ-algebra, $T \subseteq \mathcal{W}$, $Y, Y_0, Y_1 : \mathcal{W} \to \mathbb{R}$, and $W_i : \Omega \to \mathcal{W}$. Write $e^* = \nu[\mathbf{1}_T \mid m]$, $\mu_a^* = \nu[Y_a \mid m]$, $\lVert f \rVert_2^2 = \int f^2 \, d\nu$, and let $\psi$ be the AIPW score $\psi(e, g_0, g_1) = g_1 - g_0 + \mathbf{1}_T (Y - g_1)/e - \mathbf{1}_{T^c} (Y - g_0)/(1 - e)$. Let $K \in \mathbb{N}$ and let $\mathrm{fold} : \mathbb{N} \to \mathbb{N} \to \{0, \dots, K-1\}$ be a fold assignment, $\mathrm{fold}(n, i)$ being the fold of unit $i$ at sample size $n$. Write $U_{n,k}$ for the training data $(W_i)_{i < n,\ \mathrm{fold}(n,i) \ne k}$. Assume

- consistency $Y = \mathbf{1}_T Y_1 + \mathbf{1}_{T^c} Y_0$ $\nu$-a.e., and $Y_0, Y_1 \in L^2(\nu)$;
- strong overlap $\varepsilon_0 \le e^* \le 1 - \varepsilon_0$ $\nu$-a.e. for some $\varepsilon_0 > 0$;
- bounded conditional variances $\nu[(Y_a - \mu_a^*)^2 \mid m] \le C$ $\nu$-a.e. for $a = 0, 1$;
- the fitted nuisances $\hat e_{n,k}(u), \hat g_{0,n,k}(u), \hat g_{1,n,k}(u)$ satisfy, for all $n, k$ and training values $u$: $\hat e_{n,k}(u)$ is strongly $m$-measurable, $\hat g_{a,n,k}(u) \in L^2(\nu)$, and $\varepsilon \le \hat e_{n,k}(u) \le 1 - \varepsilon$ everywhere for a fixed $\varepsilon > 0$;
- for every fold $k$, in $P$-measure, $\lVert e^* - \hat e_{n,k}(U_{n,k}) \rVert_2^2 \to 0$, $\lVert \mu_0^* - \hat g_{0,n,k}(U_{n,k}) \rVert_2^2 \to 0$ and $\lVert \mu_1^* - \hat g_{1,n,k}(U_{n,k}) \rVert_2^2 \to 0$.

Then for every fold $k$ the fitted AIPW score is $L^2$-consistent for the oracle score:

$$\bigl\lVert \psi(\hat e_{n,k}(U_{n,k}), \hat g_{0,n,k}(U_{n,k}), \hat g_{1,n,k}(U_{n,k})) - \psi(e^*, \mu_0^*, \mu_1^*) \bigr\rVert_2^2 \to 0 \quad \text{in } P\text{-measure}.$$
