# Threshold stability of desert, grassland and forest equilibria in a tree–grass fire model

**Model.** Let $G$ and $T$ be grass and tree biomass under mean annual rainfall $\mathbf W$ and targeted fire frequency $f\ge0$:

$$
\begin{aligned}
\frac{dG}{dt}&=g_G(\mathbf W)\,G\Big(1-\frac{G}{K_G(\mathbf W)}\Big)-\delta_GG-\eta_{TG}(\mathbf W)\,TG-\lambda_{fG}(\mathbf W)\,fG,\\
\frac{dT}{dt}&=g_T(\mathbf W)\,T\Big(1-\frac{T}{K_T(\mathbf W)}\Big)-\delta_TT-f\,\vartheta(T)\,\omega(G)\,T,
\end{aligned}
$$

with $g_X(\mathbf W)=\gamma_X\mathbf W/(b_X+\mathbf W)$, fire intensity $\omega(G)=G^2/(G^2+\alpha^2)$ and tree fire sensitivity $\vartheta(T)=\lambda_{fT}^{\min}+(\lambda_{fT}^{\max}-\lambda_{fT}^{\min})e^{-pT}$. The sign of $\eta_{TG}$ distinguishes tree-on-grass competition ($\eta_{TG}>0$), facilitation ($\eta_{TG}<0$) and neutrality ($\eta_{TG}=0$).

**Thresholds.** Set $\mathcal R^1_{\mathbf W}=g_T/\delta_T$, $\mathcal R^2_{\mathbf W}=g_G/(\delta_G+\lambda_{fG}f)$, $T^*=K_T(1-1/\mathcal R^1_{\mathbf W})$, $G^*=K_G(1-1/\mathcal R^2_{\mathbf W})$, and

$$
\mathcal R_G=\frac{g_T}{\delta_T+\lambda_{fT}^{\max}f\,\omega(G^*)},\qquad \mathcal R_F=\frac{g_G}{\eta_{TG}T^*+\delta_G+\lambda_{fG}f},\qquad \mathcal Q_F=\frac{g_G-\eta_{TG}T^*}{\delta_G+\lambda_{fG}f}.
$$

The desert $\mathbf E_0=(0,0)$ always exists; the forest $\mathbf E_F=(0,T^*)$ exists iff $\mathcal R^1_{\mathbf W}>1$ and the grassland $\mathbf E_G=(G^*,0)$ iff $\mathcal R^2_{\mathbf W}>1$.

**Theorem (hyperbolic case).**
1. $\mathbf E_0$ is locally asymptotically stable if $\mathcal R^1_{\mathbf W}<1$ and $\mathcal R^2_{\mathbf W}<1$, and unstable if either exceeds $1$.
2. $\mathbf E_G$ is locally asymptotically stable if $\mathcal R_G<1$ and unstable if $\mathcal R_G>1$.
3. Under competition or neutrality ($\eta_{TG}\ge0$), $\mathbf E_F$ is locally asymptotically stable if $\mathcal R_F<1$ and unstable if $\mathcal R_F>1$; under facilitation ($\eta_{TG}<0$) the same holds with $\mathcal Q_F$ in place of $\mathcal R_F$.

Consequently the appearance of $\mathbf E_F$ or $\mathbf E_G$ destabilizes $\mathbf E_0$, so vegetation and bare soil are never bistable.

## Expansion

The Jacobian at each boundary equilibrium is triangular, so stability reduces to the signs of two per-capita growth rates. At $\mathbf E_G$ the invading tree's rate is $g_T-\delta_T-f\vartheta(0)\omega(G^*)$ with $\vartheta(0)=\lambda^{\max}_{fT}$, giving $\mathcal R_G$; at $\mathbf E_F$ the invading grass's rate is $g_G-\delta_G-\lambda_{fG}f-\eta_{TG}T^*$, which yields $\mathcal R_F$ when $\eta_{TG}\ge0$ (loss in the denominator) and $\mathcal Q_F$ when $\eta_{TG}<0$ (gain in the numerator). Each threshold is a production-to-loss ratio, which is what lets rainfall and fire gradients be read off as threshold crossings.

## Proof depends on

- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)
- [Lyapunov's indirect method, instability](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)

## Sources

- Ivric Valaire Yatat Djeumen, Yves Dumont, Anna Doizy, P. Couteron, "On the usefulness of a minimalistic model to study tree-grass biomass distributions along biogeographic gradients in the savanna biome", arXiv:2005.05654: Section 2 (model), Section 3 (thresholds); Appendix A, Theorem 1 (stability of trivial equilibria, hyperbolic case) and Remark 1. <https://doi.org/10.48550/arXiv.2005.05654>
- Published version: I. V. Yatat Djeumen, Y. Dumont, A. Doizy, P. Couteron, "A minimalistic model of vegetation physiognomies in the savanna biome", Ecological Modelling 440 (2021), 109381, <https://doi.org/10.1016/j.ecolmodel.2020.109381>.
