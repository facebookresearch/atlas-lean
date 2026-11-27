# Invasion reproduction numbers for two strains with asymmetric temporary immunity

**Model.** A population of constant size $N$ is split into susceptibles $S$, individuals infected with strain $j\in\{1,2\}$ ($I_j$) and individuals temporarily immune after strain $j$ ($R_j$). Strain $j$ has transmission rate $\beta_j$, recovery rate $\gamma_j$ and immunity-waning rate $\sigma_j$ (mean immunity period $\sigma_j^{-1}$). Recovery from strain 1 gives no protection against strain 2, while recovery from strain 2 protects against strain 1 with degree $\epsilon\in[0,1]$:

$$\begin{aligned}
\dot S&=-\tfrac{S}{N}(\beta_1I_1+\beta_2I_2)+\sigma_1R_1+\sigma_2R_2,\\
\dot I_1&=\tfrac{\beta_1}{N}I_1\big(S+(1-\epsilon)R_2\big)-\gamma_1I_1,\qquad \dot I_2=\tfrac{\beta_2}{N}I_2(S+R_1)-\gamma_2I_2,\\
\dot R_1&=\gamma_1I_1-\sigma_1R_1-\tfrac{\beta_2}{N}R_1I_2,\qquad \dot R_2=\gamma_2I_2-\sigma_2R_2-\tfrac{\beta_1}{N}(1-\epsilon)R_2I_1 .
\end{aligned}$$

**Reproduction numbers.** $\mathscr{R}_j=\beta_j/\gamma_j$, $\mathscr{R}_0=\max\{\mathscr{R}_1,\mathscr{R}_2\}$, and the invasion numbers

$$\mathscr{R}_{21}=\frac{\mathscr{R}_2}{\mathscr{R}_1}\cdot\frac{\beta_1+\sigma_1}{\gamma_1+\sigma_1},\qquad \mathscr{R}_{12}=\frac{\mathscr{R}_1}{\mathscr{R}_2}\cdot\frac{(1-\epsilon)\beta_2+\epsilon\gamma_2+\sigma_2}{\gamma_2+\sigma_2},$$

the expected secondary cases of strain 2 (resp. 1) introduced into a population at the endemic equilibrium of strain 1 (resp. 2) alone.

**Statements.**
1. *(Coexistence.)* The model has a steady state with $I_1>0$ and $I_2>0$ if and only if $\min\{\mathscr{R}_1,\mathscr{R}_2,\mathscr{R}_{12},\mathscr{R}_{21}\}>1$, and this coexistence state is unique whenever it exists.
2. *(Quasi-steady-state reduction.)* Assume strain 1 relaxes instantly to its endemic level given $(I_2,R_2)$, $I_1=\omega(I_2,R_2)$. The reduced planar system for $(I_2,R_2)$ leaves $\Lambda=\{I_2,R_2\ge0,\ I_2+R_2\le N\}$ invariant. If $\mathscr{R}_1,\mathscr{R}_2,\mathscr{R}_{21}>1$ and $\epsilon\in\{0,1\}$, its nullclines intersect exactly once in the interior of $\Lambda$, at a locally exponentially stable state that attracts every interior trajectory. At that state the original strain persists ($\bar I_1>0$, with $\bar I_2+\epsilon\bar R_2<N(1-1/\mathscr{R}_1)$) if $\mathscr{R}_{12}>1$, and is excluded ($\bar I_1=0$) if $\mathscr{R}_{12}<1$.
3. *(Interpretation.)* Even with $\mathscr{R}_1=\mathscr{R}_2$, a shorter immunity period of the resident strain (large $\sigma_1$) makes $\mathscr{R}_{21}$ large, and strong cross-protection from the invader ($\epsilon\to1$) lowers $\mathscr{R}_{12}$; asymmetry in immunity periods alone can therefore decide competitive outcomes.

## Expansion

At the strain-1-only equilibrium the susceptible pool available to strain 2 is $S+R_1$, because strain-1 immunity does not protect against strain 2; at that equilibrium $S^*+R_1^*=N\frac{\beta_1+\sigma_1}{\mathscr{R}_1(\gamma_1+\sigma_1)}$, so strain 2 has invasion number $\mathscr{R}_2(S^*+R_1^*)/N=\mathscr{R}_{21}$ by the next-generation method. Symmetrically, strain 1 sees only $S+(1-\epsilon)R_2$ at the strain-2 equilibrium. Coexistence requires mutual invasibility, and uniqueness follows by reducing the steady-state equations to a single monotone equation. In the reduced model, the nullcline monotonicity and a modified Dulac criterion (valid across the curve where $\omega$ switches between its endemic branch and $0$) exclude periodic orbits, so the unique interior state is globally attracting in $\Lambda$.

## Sources

- Matthew D. Johnston, Bruce Pell and David A. Rubel, "A two-strain model of infectious disease spread with asymmetric temporary immunity periods and partial cross-immunity", Mathematical Biosciences and Engineering 20 (2023), 16083–16113, <https://doi.org/10.3934/mbe.2023718>; numbering as in arXiv:2306.15011: model (SIR-partial), reproduction numbers (r), Theorems 1-3, Lemmas 5-6 and Appendix A.
