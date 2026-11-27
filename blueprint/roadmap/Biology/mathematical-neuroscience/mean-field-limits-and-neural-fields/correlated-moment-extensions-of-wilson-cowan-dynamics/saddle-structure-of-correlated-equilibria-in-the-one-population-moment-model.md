# Saddle structure of correlated equilibria in the one-population moment model

**Model.** $M$ neural populations with Markovian (quiescent/active) firing, effective weights $w_{ij}$, decay rates $\alpha_i>0$, inputs $I_i$ and smooth sigmoidal gain functions $f_i$. Truncating the moment hierarchy of the master equation at second order (Bressloff's system-size expansion, or the Buice–Cowan normal-ordered cumulant expansion) and letting the population sizes $N_i\to\infty$ in the rescaled variables, both closures converge to the **infinite-size model** for the mean activities $\nu_i$ and the correlations $\Delta_{ij}$:

$$
\begin{aligned}
\dot\nu_i&=-\alpha_i\nu_i+f_i(s_i)+\tfrac12 f_i''(s_i)\sum_{k,l}w_{ik}w_{il}\Delta_{kl},\qquad s_i=\sum_j w_{ij}\nu_j+I_i,\\
\dot\Delta_{ij}&=-(\alpha_i+\alpha_j)\Delta_{ij}+\sum_k\big[f_i'(s_i)w_{ik}\Delta_{kj}+f_j'(s_j)w_{jk}\Delta_{ki}\big].
\end{aligned}
$$

With $\Delta\equiv0$ the mean equation is the Wilson–Cowan (WC) system $\dot\nu_i=-\alpha_i\nu_i+f_i(s_i)$. For finite $N_i$ the Bressloff closure adds the source $\frac{1}{N_i}[\alpha_i\nu_i+f_i(s_i)]\delta_{ij}$ to the correlation equation (the Buice–Cowan closure adds terms of order $1/N_j$ proportional to $f_i'(s_i)w_{ij}\nu_j$), which unfolds the degenerate bifurcations of the infinite-size model.

For one population ($M=1$) the infinite-size model is planar:

$$
\dot\nu=-\alpha\nu+f(s)+\tfrac12 f''(s)w^2\Delta,\qquad \dot\Delta=2\big(-\alpha+wf'(s)\big)\Delta,\qquad s=w\nu+I .
$$

A state is **acceptable** if $\nu\ge0$ and $\Delta\ge0$ (correlations are limits of variances).

**Theorem (Touboul–Ermentrout, Theorem 2).** The one-population infinite-size model has no acceptable stable fixed point with $\Delta>0$. Precisely, a fixed point with $\Delta\ne0$ requires $wf'(s^*)=\alpha$ at $s^*=w\nu^*+I$; if $f''(s^*)\ne0$ it is unique on that line,

$$
\Delta^*=\frac{2\big(\alpha\nu^*-f(s^*)\big)}{w^2f''(s^*)},
$$

and its Jacobian

$$
\begin{pmatrix}\tfrac12 f^{(3)}(s^*)w^3\Delta^* & \tfrac12 f''(s^*)w^2\\ 2f''(s^*)w^2\Delta^* & 0\end{pmatrix}
$$

has determinant $-f''(s^*)^2w^4\Delta^*<0$ whenever $\Delta^*>0$, so the fixed point is a saddle; if $f''(s^*)=0$ there is a line of non-hyperbolic fixed points with a zero eigenvalue.

**Consequence.** By Poincaré index arguments there are no acceptable limit cycles either (a cycle in $\{\Delta>0\}$ would have to enclose fixed points of total index $+1$, but all such points are saddles of index $-1$). Hence in one population the only stable behaviors are the uncorrelated stable equilibria of the scalar WC equation; genuinely correlation-induced attractors (new cycles with roughly half the WC period, extra bistability) require at least two populations.

## Depends on

- [Stability of uncorrelated Wilson–Cowan solutions in the infinite-size moment model](stability-of-uncorrelated-wilson-cowan-solutions-in-the-infinite-size-moment-model.md)

## Proof sketch

Setting $\dot\Delta=0$ with $\Delta\neq0$ pins $\nu^*$ by $wf'(w\nu^*+I)=\alpha$ independently of $\Delta$, and then the mean equation is linear in $\Delta$. Using $wf'(s^*)=\alpha$ to simplify the linearization kills the $(2,2)$ entry, and the off-diagonal product $f''(s^*)^2w^4\Delta^*$ makes the determinant negative for every positive correlation.

## Sources

- Jonathan D. Touboul and G. Bard Ermentrout, "Finite-size and correlation-induced effects in mean-field dynamics", *Journal of Computational Neuroscience* 31 (2011), 453–484, <https://doi.org/10.1007/s10827-011-0320-5>. Preprint version: arXiv:1008.2839 (2010), <https://doi.org/10.48550/arXiv.1008.2839>.
