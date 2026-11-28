# Savanna equilibria and limit cycles under tree–grass facilitation

**Model.** Let $G$ and $T$ be grass and tree biomass under mean annual rainfall $\mathbf W$ and targeted fire frequency $f\ge0$:

$$
\begin{aligned}
\frac{dG}{dt}&=g_G(\mathbf W)\,G\Big(1-\frac{G}{K_G(\mathbf W)}\Big)-\delta_GG-\eta_{TG}(\mathbf W)\,TG-\lambda_{fG}(\mathbf W)\,fG,\\
\frac{dT}{dt}&=g_T(\mathbf W)\,T\Big(1-\frac{T}{K_T(\mathbf W)}\Big)-\delta_TT-f\,\vartheta(T)\,\omega(G)\,T,
\end{aligned}
$$

with $g_X(\mathbf W)=\gamma_X\mathbf W/(b_X+\mathbf W)$, fire intensity $\omega(G)=G^2/(G^2+\alpha^2)$ and tree fire sensitivity $\vartheta(T)=\lambda_{fT}^{\min}+(\lambda_{fT}^{\max}-\lambda_{fT}^{\min})e^{-pT}$. The sign of $\eta_{TG}$ distinguishes tree-on-grass competition ($\eta_{TG}>0$), facilitation ($\eta_{TG}<0$) and neutrality ($\eta_{TG}=0$).

A *savanna equilibrium* $\mathbf E_S=(G_*,T_*)$ with $G_*,T_*>0$ solves $g_G(1-G_*/K_G)=\delta_G+\lambda_{fG}f+\eta_{TG}T_*$ and $g_T(1-T_*/K_T)=\delta_T+f\vartheta(T_*)\omega(G_*)$.

**Proposition (number of savanna equilibria).** Under competition ($\eta_{TG}>0$) the system has between zero and four savanna equilibria; under facilitation ($\eta_{TG}<0$) between zero and five; in the neutral case ($\eta_{TG}=0$) between zero and two. Several of them may be simultaneously locally asymptotically stable (multistability).

**Theorem (Poincaré–Bendixson alternative).** If every equilibrium is unstable, then either all solutions converge to a periodic orbit or the system has a homoclinic or heteroclinic cycle.

**Theorem (Hopf bifurcation in fire frequency).** If a savanna equilibrium exists and the trace of its Jacobian crosses zero transversally at $f=f_h$ with positive determinant, then a Hopf bifurcation occurs at $f_h$; it is supercritical (a unique stable limit cycle) if the first Lyapunov coefficient $\sigma$ is negative and subcritical (a unique unstable cycle) if $\sigma>0$.

**Fire-free case.** If $f=0$ there is at most one savanna equilibrium, namely $T_*=K_T\big(1-\delta_T/g_T(\mathbf W)\big)$, $G_*=K_G\big(1-(\delta_G+\eta_{TG}T_*)/g_G(\mathbf W)\big)$ (Remark 3(i)), and it exists exactly when both are positive (in particular none exists when $g_T(\mathbf W)\le\delta_T$); grassland–forest, grassland–savanna and forest–savanna bistability cannot occur, and $B(T,G)=1/(TG)$ is a Dulac function, so there are no periodic orbits, homoclinic or heteroclinic cycles.

## Expansion

Eliminating $G_*$ from the grass isocline (a line in $(G,T)$) and substituting into the tree isocline gives a scalar equation in which the sigmoid $\omega$ and exponential $\vartheta$ create several sign changes, hence the bound on the number of roots; the extra root under facilitation comes from the grass isocline then having positive slope. With $f=0$ the system is a Lotka–Volterra competition model in which divergence of $(\dot G,\dot T)/(TG)$ is negative, so Dulac's criterion excludes cycles. Fire couples the two isoclines nonmonotonically, which is what allows trace sign changes and oscillations; the source notes that cycles were not observed for the parameter ranges it calibrated along rainfall gradients.

## Depends on

- [Threshold stability of desert, grassland and forest equilibria in a tree–grass fire model](threshold-stability-of-desert-grassland-and-forest-equilibria.md)

## Proof depends on

- [Poincaré–Bendixson theorem](../../../../../Dynamics/low-dimensional-dynamics/poincar-bendixson-theorem/poincare-bendixson.md)

## Sources

- Ivric Valaire Yatat Djeumen, Yves Dumont, Anna Doizy, P. Couteron, "On the usefulness of a minimalistic model to study tree-grass biomass distributions along biogeographic gradients in the savanna biome", arXiv:2005.05654: Section 3, Proposition 1 (number of savanna equilibria); Appendix A, Theorems 3–5 (savanna stability, Poincaré–Bendixson alternative, Hopf bifurcation) and Remark 3 (fire-free case). <https://doi.org/10.48550/arXiv.2005.05654>
- Published version: I. V. Yatat Djeumen, Y. Dumont, A. Doizy, P. Couteron, "A minimalistic model of vegetation physiognomies in the savanna biome", Ecological Modelling 440 (2021), 109381, <https://doi.org/10.1016/j.ecolmodel.2020.109381>.
