# Traveling waves of a tree–grass–grazer–browser savanna system

**Model.** Dimensionless biomasses of woody plants $W$, grass $H$, grazers $G$ and browsers $B$ on the line satisfy

$$\begin{aligned}
W_t &= d_W W_{xx} + r_W W(1-W-\kappa_1 H) - c_W BW, & H_t &= d_H H_{xx} + r_H H(1-H-\kappa_2 W) - c_H GH,\\
G_t &= d_G G_{xx} + e_H G(H-G), & B_t &= d_B B_{xx} + e_W B(W-B),
\end{aligned}$$

with diffusion (migration) rates $d_\bullet>0$, plant growth rates $r_W, r_H$, tree–grass competition coefficients $\kappa_1,\kappa_2$, consumption coefficients $c_W, c_H$ and herbivore conversion rates $e_W, e_H$. It has a unique positive coexistence state $(W^*,H^*,G^*,B^*)$. Set

$$s_m = \max\{2\sqrt{d_Wr_W},\,2\sqrt{d_Hr_H}\},\quad s_{M_1} = \min\Big\{d_B\sqrt{\tfrac{r_W}{d_B-d_W}},\,2\sqrt{d_Be_W\big(1-\kappa_1-\tfrac{c_W}{r_W}\big)}\Big\},\quad s_{M_2} = \min\Big\{d_G\sqrt{\tfrac{r_H}{d_G-d_H}},\,2\sqrt{d_Ge_H\big(1-\kappa_2-\tfrac{c_H}{r_H}\big)}\Big\}.$$

**Theorem.** Assume $d_B>2d_W>0$, $d_G>2d_H>0$, $1-\kappa_1-\frac{c_W}{r_W}>0$, $1-\kappa_2-\frac{c_H}{r_H}>0$ and $s_m<\min\{s_{M_1},s_{M_2}\}$. Then for every speed $s$ with $s_m<s<\min\{s_{M_1},s_{M_2}\}$ there is a positive smooth traveling wave $(W,H,G,B)(x+st)$ with

$$\lim_{\xi\to-\infty}(W,H,G,B)(\xi) = (0,0,0,0), \qquad \lim_{\xi\to+\infty}(W,H,G,B)(\xi) = (W^*,H^*,G^*,B^*),$$

describing invasion of an empty habitat by the full savanna community. If instead $\kappa_1=0$, $d_B>2d_W$, $1-\frac{c_W}{r_W}>0$, $1-\kappa_2-\frac{c_H}{r_H}>0$ and $s_m<s<s_{M_1}$, there is a positive traveling wave connecting the grass–grazer state $(0,H_*,G_*,0)$ to the coexistence state, describing invasion of grassland by trees and browsers.

## Expansion

Linearising at the extinction state, the plants spread with Fisher–KPP speeds $2\sqrt{d_Wr_W}$ and $2\sqrt{d_Hr_H}$, so speeds above $s_m$ allow exponentially decaying profiles at $-\infty$; the upper bounds keep the herbivores, which follow their food plants, from outrunning them. Existence follows from constructing upper and lower solutions in a bounded invariant set and a Schauder fixed-point argument on truncated domains, while convergence to the coexistence state at $+\infty$ uses a Lyapunov-type functional for the travelling-wave system.

## Sources

- C.-C. Chen, T.-Y. Hsiao, S.-C. Wang, "Savanna dynamics with grazing, browsing, and migration effects", *SIAM Journal on Applied Dynamical Systems* 24(4) (2025), 2950–2976, Section 2, Theorems 2.1–2.2, <https://doi.org/10.1137/25m1725693> (preprint arXiv:2501.06549).
