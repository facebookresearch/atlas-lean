# Mass-structured population balance model of yeast in wine fermentation

Let $W(m,t)$ be the number density of budding yeast cells of mass $m\in(m_{\min},m_{\max})$ at time $t$, and let $N,S,O,E$ be the nitrogen, sugar, oxygen and ethanol concentrations. The cell density obeys the population balance (growth–fragmentation) equation

$$
\partial_tW=-\partial_m\big(r_\epsilon(m,N,S,O)W\big)+2\int_{m_{\min}}^{m_{\max}}p(m,m')\Gamma(m')W(m',t)\,dm'-\Gamma(m)W-\Phi(E)W-k_dW,
$$

with $W(m,0)=W_0(m)$ and no-flux conditions $r_\epsilon W=0$ at $m=m_{\min}$ and $m=m_{\max}$. Here:

- the single-cell growth rate is $r_\epsilon=\mu_{\max}(T)\frac{N}{K_N+N}\frac{S}{K_{S_1}+S}\left(\frac{O}{K_O+O}+\epsilon\right)m$ with $\epsilon>0$, so that growth continues on other nutrients without oxygen;
- the division rate $\Gamma(m)$ is $0$ for $m\le m_t$ (transition mass), $\gamma e^{-\delta(m-m_d)^2}$ for $m_t<m<m_d$ (division mass), and $\gamma$ beyond;
- the partition kernel $p(m,m')=\lambda e^{-\beta(m-m_t)^2}+\lambda e^{-\beta(m-m'+m_t)^2}$ for $m'>m$, $m'>m_t$ (and $0$ otherwise) has two peaks, one at the daughter size $m_t$ and one at the mother remainder $m'-m_t$; it should satisfy $\int p(m,m')\,dm=1$ and the mass-conservation symmetry $p(m,m')=p(m'-m,m')$;
- $\Phi(E)=\left(\tfrac12+\tfrac1\pi\arctan(k_{d_1}(E-tol))\right)k_{d_2}(E-tol)^2$ is ethanol-induced death above a tolerance $tol$, and $k_d$ is natural death.

The substrates are consumed by the whole population through integral terms:

$$
N'=-k_1\!\int r_\epsilon W\,dm,\quad O'=-k_4\!\int r\,W\,dm,\quad S'=-\!\int\big(k_2q_E+k_3r_\epsilon\big)W\,dm,\quad E'=\int q_EW\,dm,
$$

where $r$ is $r_\epsilon$ with $\epsilon=0$ and $q_E=\beta_{\max}(T)\frac{S}{K_S+S}\frac{K_E(T)}{K_E(T)+E}m$ is ethanol production with product inhibition. The rates $\mu_{\max},\beta_{\max},K_E$ are affine in the fermentation temperature $T$.

## Expansion

The model couples a hyperbolic partial integro-differential equation for the cell-mass distribution with a system of integro-differential equations for the substrates. The integral term is the birth of mass-$m$ cells from division of larger cells, counted twice because each division produces a daughter and a mother; the loss term $-\Gamma W$ removes the dividing cells. Integrating the PBE over mass recovers an unstructured logistic-type model for total biomass, which is the ODE fermentation model this structured version refines. Simulations reproduce measured sugar, nitrogen and ethanol trajectories in white-wine fermentations.

## Sources

- C. Schenk, V. H. Schulz, "Existence, Uniqueness and Numerical Modeling of Wine Fermentation Based on Integro-Differential Equations", Section "Model Derivation". <https://doi.org/10.48550/arXiv.2104.06777>
