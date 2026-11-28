# Effective population size from remeeting times and transient amplifiers of death-Birth selection

**Model.** A population of $N$ individuals occupies the vertices of a weighted, undirected, connected graph $G$ with edge weights $w_{ij}=w_{ji}\ge0$ and no self-loops. Residents have fitness $1$ and mutants fitness $r>0$. Under **death-Birth (dB) updating**, an individual is chosen uniformly at random to die and a neighbor $j$ of the vacated vertex $i$ is chosen to reproduce into it with probability proportional to $w_{ij}$ times its fitness. $\rho_G(r)$ is the fixation probability of a single mutant placed uniformly at random. On the complete graph $\rho_{K_N}(1+\delta)=\frac1N+\delta\frac{N-2}{2N}+O(\delta^2)$.

**Coalescence quantities.** Let $p_{ij}=w_{ij}/w_i$ with $w_i=\sum_jw_{ij}$, and $\pi_i=w_i/\sum_jw_j$ the stationary distribution of the random walk. Expected coalescence times $\tau_{ij}$ of two walkers (one of the two moves per step) solve

$$
\tau_{ii}=0,\qquad \tau_{ij}=1+\tfrac12\sum_k\bigl(p_{ik}\tau_{jk}+p_{jk}\tau_{ik}\bigr)\quad(i\ne j),
$$

the remeeting times are $\tau_i=1+\sum_jp_{ij}\tau_{ij}$, and $\sum_i\pi_i^2\tau_i=1$.

**Theorem (weak-selection expansion).** For every such graph,

$$
\rho_G(1+\delta)=\frac1N+\delta\,\frac{N_{\mathrm{eff}}-2}{2N}+O(\delta^2),\qquad N_{\mathrm{eff}}:=\sum_{i\in G}\pi_i\tau_i .
$$

So $G$ amplifies weak selection iff $N_{\mathrm{eff}}>N$ and suppresses it iff $N_{\mathrm{eff}}<N$.

**Theorem (weak-selection isothermal theorem).** If $G$ is isothermal ($w_i$ the same for all $i$), then $\rho_G(1+\delta)=\rho_{K_N}(1+\delta)+O(\delta^2)$.

**Theorem (Separated Hubs).** A graph is a **transient amplifier** if $\rho_G<\rho_{K_N}$ for $r<1$ and for $r>r^*$ but $\rho_G>\rho_{K_N}$ on $(1,r^*)$, and a **reducer of fixation** if $\rho_G<\rho_{K_N}$ for all $r\ne1$. In the limit $\varepsilon\to0$ of its weak edges, the Separated Hubs graph $SH_{m,n,h}$ is a suppressor for $n\le h$, a reducer for $n=h+1$ and a transient amplifier for $n\ge h+2$; transient amplifiers of dB updating therefore exist, although no (non-transient) amplifier does. For the star with $n$ leaves, $N_{\mathrm{eff}}=4n/(n+1)<N$, a suppressor.

## Expansion

Write the fixation probability as an expectation over the neutral process of the selection-induced drift of the mutant frequency. To first order in $\delta$ this drift is a linear combination of two-point correlations of mutant indicators at neighboring vertices, averaged over the neutral stationary distribution conditioned on fixation; under neutral dB dynamics these correlations equal identity-by-descent probabilities, which are linear in the coalescence times $\tau_{ij}$ of the ancestral random walks. Collecting terms gives $(N_{\mathrm{eff}}-2)/(2N)$ with $N_{\mathrm{eff}}=\sum_i\pi_i\tau_i$. For isothermal graphs $\pi_i=1/N$, and $\sum_i\pi_i^2\tau_i=1$ gives $N_{\mathrm{eff}}=N$, recovering the complete-graph coefficient. For $SH_{m,n,h}$, weak-selection amplification comes from $N_{\mathrm{eff}}>N$, while for large $r$ a general bound for dB updating forces $\rho_G<\rho_{K_N}$, giving transience; the reducer case uses convexity of the complete-graph fixation function in an auxiliary variable.

## Proof depends on

- [First-order weak-selection expansion of fixation probability](../../../../population-genetics/moran-model/weak-selection-fixation-probabilities/weak-selection-fixation-probability-expansion.md)
- [Reproductive values and neutral fixation probability](../../../../population-genetics/moran-model/weak-selection-fixation-probabilities/reproductive-value-and-neutral-fixation.md)

## Sources

- B. Allen, C. Sample, R. Jencks, J. Withers et al., "Transient amplifiers of selection and reducers of fixation for death-Birth updating on graphs", arXiv:1906.01036 (2019), Results (Eqs. for $\tau_{ij}$, $\tau_i$, $N_{\mathrm{eff}}$ and the weak-selection expansion; isothermal theorem; Separated Hubs theorem) and appendices "Method for weak selection" and "Mathematical lemmas", <https://doi.org/10.48550/arXiv.1906.01036>.
