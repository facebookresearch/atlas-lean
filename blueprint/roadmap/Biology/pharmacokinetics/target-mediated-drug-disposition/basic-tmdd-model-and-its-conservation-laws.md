# Basic TMDD model and its conservation laws

**Model.** Let $L(t)$, $R(t)$ and $RL(t)$ be the concentrations of free ligand (drug), free target (receptor) and ligand–target complex in the central compartment. The basic target-mediated drug disposition model is

$$
\begin{aligned}
\frac{dL}{dt} &= k_f - k_{on} L R + k_{off} RL - k_{e(L)} L,\\
\frac{dR}{dt} &= k_{in} - k_{out} R - k_{on} L R + k_{off} RL,\\
\frac{dRL}{dt} &= k_{on} L R - k_{off} RL - k_{e(RL)} RL,
\end{aligned}
$$

with all rate constants positive except the infusion rate $k_f \ge 0$. Target is synthesized at zero-order rate $k_{in}$ and degraded at rate $k_{out}$; free ligand is eliminated at rate $k_{e(L)}$ and the complex is internalized at rate $k_{e(RL)}$. Before dosing the system is at baseline $L = RL = 0$, $R = R_0 := k_{in}/k_{out}$. A bolus dose gives $k_f = 0$, $L(0) = L_0 = D/V_c$; a constant-rate infusion gives $k_f = \mathrm{In}_L/V_c > 0$, $L(0) = 0$.

**Conservation laws.** Put $L_{tot} = L + RL$ and $R_{tot} = R + RL$. Then

$$\frac{dL_{tot}}{dt} = k_f - k_{e(L)} L - k_{e(RL)} RL, \qquad \frac{dR_{tot}}{dt} = k_{in} - k_{out} R - k_{e(RL)} RL,$$

in which the binding rates $k_{on}, k_{off}$ no longer appear. In particular, for a bolus dose ($k_f = 0$) the total ligand $L_{tot}(t)$ is non-increasing.

## Expansion

Summing the ligand and complex equations cancels the binding and unbinding terms, and likewise for target and complex. With high affinity ($k_{off}/k_{on}$ small relative to $R_0$ and $L_0$) a bolus profile shows distinct phases: fast binding, linear elimination of excess ligand, a target-mediated phase, and a terminal phase; the conservation laws and the target bounds organize their analysis, and in suitable regimes a Michaelis–Menten elimination model approximates the full system.

## Sources

- L. A. Peletier and J. Gabrielsson, "Dynamics of target-mediated drug disposition: characteristic profiles and parameter identification", *Journal of Pharmacokinetics and Pharmacodynamics* (2012), system (1), baseline steady state (2), totals (3) and conservation laws (4). <https://doi.org/10.1007/s10928-012-9260-6> (PMC3446204)
