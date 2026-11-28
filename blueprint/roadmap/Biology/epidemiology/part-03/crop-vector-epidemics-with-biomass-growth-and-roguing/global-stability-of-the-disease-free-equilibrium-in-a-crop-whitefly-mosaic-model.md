# Global stability of the disease-free equilibrium in a crop–whitefly mosaic model

**Statement.** In the crop–whitefly mosaic model with biomass growth $r_p(V)=r/(1+\phi V)$, maintenance losses $m_h\le m_i$, harvest $k_p$, roguing rate $\gamma$ and vector birth $\alpha_v(I_p)$, let $E_{DFE}=(P^*,0,V^*,0)$ with $V^*=(\alpha_v(0)-\mu_1)/\mu_2$, $P^*=(r_p(V^*)-k_p)/m_h$, and

$$
\mathcal J_0=\frac{\beta_{pv}\beta_{vp}P^*V^*}{\big((m_i-m_h)P^*+\gamma\big)\alpha_v(0)} .
$$

Assume $\gamma+(m_i-m_h)P^*>0$. Then the disease-free equilibrium is globally asymptotically stable in the feasible region if $\mathcal J_0\le1$ and unstable if $\mathcal J_0>1$. Since $\mathcal J_0$ and the next-generation number $\mathcal R_0$ lie on the same side of $1$, this is the global version of the $\mathcal R_0$ threshold; roguing ($\gamma$) and the infection cost ($m_i-m_h$) enter the denominator and are the levers that push $\mathcal J_0$ below $1$.

## Expansion

The proof uses the Castillo-Chavez–Feng–Huang criterion: split $x=(H_p,S_v)$ (uninfected) from $y=(I_p,I_v)$ (infected), so that $y'=g(x,y)$ with $g(x,0)=0$. On $y=0$ the vector equation is logistic, so $S_v\to V^*$, and then $H_p\to P^*$; hence $x^*=(P^*,V^*)$ is globally asymptotically stable for $x'=f(x,0)$. Next write $g(x,y)=Ay-\hat g(x,y)$ with the Metzler matrix

$$
A=\begin{pmatrix}-\big((m_i-m_h)P^*+\gamma\big)&\beta_{vp}P^*\\ \beta_{pv}V^*&-\alpha_v(0)\end{pmatrix},
$$

and use $H_p\le P^*$, $S_v\le V^*$ on the relevant region to get $\hat g\ge0$. A Metzler matrix with negative trace is Hurwitz exactly when its determinant is positive, i.e. $\mathcal J_0<1$, which yields global attraction; for $\mathcal J_0>1$ the infected subsystem has a positive eigenvalue at the DFE. Beyond the threshold the paper shows numerically that the endemic state can lose stability through a Hopf bifurcation, giving sustained oscillations in healthy biomass.

## Depends on

- [Reproduction number of a crop–whitefly mosaic model with vertical biomass transmission](reproduction-number-of-a-crop-whitefly-mosaic-model-with-vertical-biomass-transmission.md)

## Proof depends on

- [Routh–Hurwitz: a real 2 × 2 matrix is Hurwitz iff tr M < 0 < det M](../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-hurwitz-iff-trace-neg-and-det-pos.md)

## Sources

- M. Chapwanya, Y. Dumont, "Application of Mathematical Epidemiology to crop vector-borne diseases. The cassava mosaic virus disease case" (2019), Section 3.3, Theorem 3.3. <https://doi.org/10.48550/arXiv.1912.05370>
