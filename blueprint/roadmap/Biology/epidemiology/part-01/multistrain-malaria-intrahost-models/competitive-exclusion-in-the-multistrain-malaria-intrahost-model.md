# Competitive exclusion in the multistrain malaria intrahost model

**Model.** Healthy red blood cells $x$ are shared by $n$ parasite strains; strain $i$ has parasitized-cell classes $y_{1,i},\dots,y_{k,i}$, gametocytes $g_i$ and merozoites $m_i$:

$$
\begin{aligned}
\dot x &= \varphi(x) - x\sum_{i=1}^n\beta_im_i,\\
\dot y_{1,i} &= \beta_ixm_i - \alpha_{1,i}y_{1,i},\qquad \dot y_{j,i} = \gamma_{j-1,i}y_{j-1,i} - \alpha_{j,i}y_{j,i}\quad(j=2,\dots,k),\\
\dot g_i &= \delta_iy_{k,i} - \mu_{g_i}g_i,\qquad \dot m_i = r_i\gamma_{k,i}y_{k,i} - \mu_{m_i}m_i - u\beta_ixm_i,
\end{aligned}
$$

with $\varphi$ as in the one-strain model (unique stable RBC level $x^*$). For each strain let

$$
\mathcal R_0^i = \frac{r_i\beta_ix^*}{\mu_{m_i}+u\beta_ix^*}\,\frac{\gamma_{1,i}\cdots\gamma_{k,i}}{\alpha_{1,i}\cdots\alpha_{k,i}},\qquad
\bar x_i = \frac{\mu_{m_i}}{\beta_i\Big[r_i\frac{\gamma_{1,i}\cdots\gamma_{k,i}}{\alpha_{1,i}\cdots\alpha_{k,i}}-u\Big]},\qquad \mathcal T_0^i = \frac{x^*}{\bar x_i},
$$

and $\mathcal R_0=\max_i\mathcal R_0^i$.

**Theorem (competitive exclusion).**

1. The disease-free equilibrium is globally asymptotically stable iff $\mathcal R_0\le 1$.
2. If $\mathcal R_0>1$ it is unstable, and every strain with $\mathcal R_0^i>1$ has a single-strain endemic equilibrium with $x=\bar x_i$ and all other strains absent.
3. Assume $\mathcal R_0>1$ and the generic condition $\mathcal T_0^i\ne\mathcal T_0^j$ for $i\ne j$, and index strains so that $\mathcal T_0^1>\mathcal T_0^2\ge\dots\ge\mathcal T_0^n$. Then the endemic equilibrium of strain 1 is asymptotically stable and the other single-strain endemic equilibria are unstable. If moreover $u\beta_1\varphi(\bar x_1)\le\mu_{m_1}\alpha^*$ with $\alpha^*=-\max_{[0,x^*]}\varphi'$, the strain-1 equilibrium is globally asymptotically stable on the nonnegative orthant minus the $x$-axis and the face $y_1=m_1=g_1=0$: the strain that drives healthy red blood cells lowest wins and all others go extinct.

## Expansion

Each strain $i$ can persist only if the healthy-cell level exceeds its break-even density $\bar x_i$, so the strain with the smallest $\bar x_i$ (largest $\mathcal T_0^i$, the "most virulent" one) depletes the shared resource below every competitor's threshold, as in chemostat competition. The proof combines the one-strain Volterra function for strain 1 with linear functions $\beta_ix^*\langle e_{i,\omega},(-A_i)^{-1}z_i\rangle$ for the others: using $\mathcal T_0^1\bar x_1=x^*$, the derivative of $V=\mathcal T_0^1V_{EE}(x,z_1)+a\sum_{i\ge2}V_{DFE}(z_i)$ is $\mathcal T_0^1\Phi(x,z_1)+a\sum_{i\ge2}\beta_ix\,m_i(\mathcal T_0^i-\mathcal T_0^1)\le 0$, and LaSalle's principle concludes. In the nongeneric case of ties a continuum of stable endemic equilibria appears.

## Depends on

- [Global threshold dynamics of the k-stage malaria intrahost model](global-threshold-dynamics-of-the-k-stage-malaria-intrahost-model.md)

## Sources

- A. Iggidr, J.-C. Kamgang, G. Sallet, J.-J. Tewa, *Global analysis of new malaria intrahost models with a competitive exclusion principle*, arXiv:1101.0922 (2011). <https://doi.org/10.48550/arXiv.1101.0922> — Theorem 3.1 (Section 3, $n$ strains with $k$ classes) and the remarks following it. Published version: SIAM Journal on Applied Mathematics 67(1) (2006), 260–278, <https://doi.org/10.1137/050643271>; locators above refer to the arXiv version.
