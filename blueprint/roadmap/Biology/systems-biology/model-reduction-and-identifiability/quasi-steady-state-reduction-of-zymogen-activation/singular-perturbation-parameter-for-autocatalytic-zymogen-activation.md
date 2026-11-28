# Singular perturbation parameter for autocatalytic zymogen activation

In intermolecular autocatalytic zymogen activation (IAZA), the active enzyme $E$ binds the zymogen $Z$ to form a complex $C$, which releases a second enzyme molecule: $Z+E\rightleftharpoons C\to2E$, with rate constants $k_1,k_{-1},k_2$. Let $w$ be the amount of zymogen converted. Mass action with $z(0)=z_0$, $e(0)=e_0$, $c(0)=w(0)=0$ gives

$$
\dot z=-k_1ez+k_{-1}c,\qquad \dot c=k_1ez-(k_{-1}+k_2)c,\qquad \dot e=-k_1ez+(k_{-1}+2k_2)c,\qquad \dot w=k_2c,
$$

with conservation laws $z+e+2c=E_T:=z_0+e_0$ and $z+c+w=z_0$. In the $(w,c)$ variables the complex equation factors as $\dot c=k_1(c-h^-(w))(c-h^+(w))$, where $h^-\le h^+$ are the two $c$-nullcline branches; $c=h^-(w)$ is the quasi-steady-state (QSS) manifold. Let $K_M=(k_{-1}+k_2)/k_1$, $K=k_2/k_1$, and

$$
\varphi=\begin{cases}\sqrt{K_M(K_M+2E_T)}, & e_0\le z_0,\\ \sqrt{(K_M+E_T)^2-4e_0z_0}, & z_0<e_0,\end{cases}
\qquad
\lambda_Z=\begin{cases}\tfrac12\big(K_M+E_T-\sqrt{K_M(K_M+2E_T)}\big), & e_0<z_0,\\ \tfrac12\big(K_M+E_T-\sqrt{(K_M+E_T)^2-4e_0z_0}\big), & z_0\le e_0.\end{cases}
$$

**Proposition.** For every solution starting in the trapping region $\Lambda^*$ of the phase plane, the distance $\mathcal E_Z=c-h^-(w)$ to the QSS manifold satisfies

$$
\mathcal E_Z^2(t)\le\mathcal E_Z^2(0)\,e^{-k_1\varphi t}+\varepsilon^2\lambda_Z^2,\qquad
\varepsilon:=\frac{E_T}{K_M+E_T}\cdot\frac{K}{\varphi}.
$$

So trajectories reach an $O(\varepsilon\lambda_Z)$ neighbourhood of the QSS manifold on the fast time scale $1/(k_1\varphi)$, and $\varepsilon\ll1$ is the condition under which QSS-based estimation of kinetic constants from progress curves is valid. When $z_0>e_0$, normal hyperbolicity of the critical manifold is lost at $w_T=(z_0-e_0)/2$, where attracting and repelling branches of $\{c=z_0-w\}$ and $\{c=e_0+w\}$ exchange stability.

## Depends on

- [Michaelis constant](../../michaelis-menten-kinetics-and-the-quasi-steady-s/michaelis-constant.md)

## Proof sketch

Differentiate $\mathcal E_Z^2$ along trajectories. In $\Lambda^*$, $c-h^+(w)\le-\varphi$, which gives the contraction term $-k_1\varphi\mathcal E_Z^2$. The drift of the manifold contributes $|D_wh^-|\,|\dot w|\le\frac{E_T}{K_M+E_T}\,k_2\lambda_Z$. Young's inequality with $\delta=k_1\varphi/2$ and Grönwall's lemma give the bound. The factorization of $\dot c$ into the two nullcline branches, common to mass-action enzyme models, is what makes the estimate sharp.

## Sources

- Justin Eilertsen, Malgorzata Anna Tyczynska and Santiago Schnell, "Hunting $\varepsilon$: The Origin and Validity of Quasi-Steady-State Reductions in Enzyme Kinetics", *SIAM Journal on Applied Dynamical Systems* 20 (2021), 2450–2481, <https://doi.org/10.1137/20m135073x>. Preprint version: arXiv:2109.03957 (2021), Section 2 (mass-action equations and conservation laws), Section 4 (Proposition 1, Eq. (epsL)), Section 5 (Proposition 2), <https://doi.org/10.48550/arXiv.2109.03957>.
