# Reproduction number of a crop–whitefly mosaic model with vertical biomass transmission

**Model.** Crop biomass $P=H_p+I_p$ (healthy, infected) and whitefly vectors $V=S_v+I_v$ (susceptible, infectious) evolve as

$$
\begin{aligned}
H_p'&=r_p(V)H_p-m_hPH_p-\beta_{vp}H_pI_v-k_pH_p,\\
I_p'&=r_p(V)I_p+\beta_{vp}H_pI_v-m_iPI_p-\gamma I_p-k_pI_p,\\
S_v'&=\alpha_v(I_p)V-(\mu_1+\mu_2V)S_v-\beta_{pv}S_vI_p,\\
I_v'&=\beta_{pv}S_vI_p-(\mu_1+\mu_2V)I_v,
\end{aligned}
$$

with all parameters positive: $r_p(V)=r/(1+\phi V)$ is biomass production (decreasing in vector load, and infected biomass produces infected biomass, i.e. vertical transmission through cuttings and growth), $m_h\le m_i$ are maintenance losses of healthy and infected biomass, $k_p$ is harvest, $\gamma$ is the roguing rate (removal of infected biomass), and $\alpha_v(I_p)=\alpha(1+\delta I_p/(1+I_p))$ is the vector birth rate, boosted by diseased plants.

**Well-posedness.** If $\alpha_v(0)>\mu_1$ and $r_p(0)>k_p$, the system defines a dynamical system on $\Omega=\{H_p,I_p,S_v,I_v\ge0:\ H_p+I_p\le P^\dagger,\ S_v+I_v\le V^\dagger\}$, with $P^\dagger=(r_p(0)-k_p)/m_h$ and $V^\dagger=(\alpha(1+\delta)-\mu_1)/\mu_2$.

**Reproduction number.** The disease-free equilibrium is $E_{DFE}=(P^*,0,V^*,0)$ with $V^*=(\alpha_v(0)-\mu_1)/\mu_2$ and $P^*=(r_p(V^*)-k_p)/m_h$ (assumed positive). Taking new infections $\mathcal F=(r_p(V)I_p+\beta_{vp}H_pI_v,\ \beta_{pv}S_vI_p)$ and transfers $\mathcal V=((m_iP+\gamma+k_p)I_p,\ (\mu_1+\mu_2V)I_v)$, the next-generation matrix has spectral radius

$$
\mathcal R_0=\tfrac12\Big(\mathcal V_0+\sqrt{\mathcal V_0^2+4\mathcal H_0}\Big),\qquad \mathcal V_0=\frac{r_p(V^*)}{(m_i-m_h)P^*+\gamma+r_p(V^*)},\quad \mathcal H_0=\frac{\beta_{pv}\beta_{vp}P^*V^*}{\alpha_v(0)\,[(m_i-m_h)P^*+\gamma+r_p(V^*)]},
$$

where $\mathcal V_0$ is the vertical (biomass-production) contribution and $\mathcal H_0$ the horizontal plant–vector–plant contribution. The DFE is locally asymptotically stable if $\mathcal R_0<1$ and unstable if $\mathcal R_0>1$. In particular, with no roguing and no extra maintenance cost of infection ($\gamma=0$, $m_i=m_h$), $\mathcal V_0=1$ and so $\mathcal R_0>1$: the disease cannot be eliminated without removing infected biomass or a fitness cost of infection. The boundary equilibria $(0,0,V^*,0)$ and $(P^\dagger,0,0,0)$ are always unstable.

**Equivalent threshold.** With

$$
\mathcal J_0=\frac{\beta_{pv}\beta_{vp}P^*V^*}{\big((m_i-m_h)P^*+\gamma\big)\alpha_v(0)},
$$

$\mathcal R_0=1\iff\mathcal H_0=1-\mathcal V_0\iff\mathcal J_0=1$, and $\mathcal R_0<1\iff\mathcal J_0<1$ whenever $(m_i-m_h)P^*+\gamma>0$; $\mathcal J_0<1$ is the positive-determinant condition for the reduced $2\times2$ Jacobian of the infected subsystem at the DFE.

## Expansion

At the DFE, $m_hP^*=r_p(V^*)-k_p$ and $\mu_1+\mu_2V^*=\alpha_v(0)$, so $F=\begin{pmatrix}r_p(V^*)&\beta_{vp}P^*\\ \beta_{pv}V^*&0\end{pmatrix}$ and $V=\operatorname{diag}\big((m_i-m_h)P^*+\gamma+r_p(V^*),\ \alpha_v(0)\big)$; the eigenvalues of $FV^{-1}$ solve $\lambda^2-\mathcal V_0\lambda-\mathcal H_0=0$. Since $\mathcal R_0$ is the positive root of $\lambda^2-\mathcal V_0\lambda-\mathcal H_0$, which is negative at $\lambda=0$, $\mathcal R_0<1$ iff the polynomial is positive at $1$, that is iff $\mathcal V_0+\mathcal H_0<1$: the additive index $\mathcal V_0+\mathcal H_0$ lies on the same side of $1$ as $\mathcal R_0$. (The index $\mathcal V_0+\sqrt{\mathcal H_0}$ does not: $\mathcal V_0=0.5$, $\mathcal H_0=0.3$ give $\mathcal R_0\approx0.85$ but $\mathcal V_0+\sqrt{\mathcal H_0}\approx1.05$.) Where the next-generation decomposition puts $r_p(V)I_p$ (into $\mathcal F$ or into $\mathcal V$) changes the number but not the threshold, which is why $\mathcal R_0$ and $\mathcal J_0$ agree at $1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [Threshold theorem, stability half, conditional decay form](../../next-generation-matrix-and-the-basic-reproductio/global-solution-decay-of-r0-lt-one.md)
- [Threshold theorem, instability half, spectral form](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-jacobian-of-one-lt-r0.md)
- [Lyapunov's indirect method, instability](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)

## Sources

- M. Chapwanya, Y. Dumont, "Application of Mathematical Epidemiology to crop vector-borne diseases. The cassava mosaic virus disease case" (2019), Section 3: Theorem 3.1 (well-posedness), Section 3.1 and Theorem 3.2 ($\mathcal R_0$ and local stability), Proposition 3.1 and Remarks 3.1 and 3.4. <https://doi.org/10.48550/arXiv.1912.05370>
