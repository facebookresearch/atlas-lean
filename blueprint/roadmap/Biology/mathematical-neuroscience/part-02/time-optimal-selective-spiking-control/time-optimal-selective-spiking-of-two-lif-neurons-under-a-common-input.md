# Time-optimal selective spiking of two LIF neurons under a common input

**Model.** Two leaky integrate-and-fire neurons with rest potential normalized to $0$ share one stimulus $u(t) \in [0, U]$:

$$\dot v_i = -a_i v_i + b_i u, \qquad a_i = \frac{1}{R_i C_i} > 0, \quad b_i = \frac{\beta_i}{C_i} > 0, \quad i = 1,2,$$

and neuron $i$ spikes when $v_i$ reaches the threshold $V_T$, after which $v_i$ resets to $0$. A guard $V_G < V_T$ is chosen below $V_T$ minus the largest synaptic kick, so a neuron kept at or below $V_G$ cannot be pushed to spike by its partner.

**Selective spiking problem (P1).** From $v(0) \in G = [0,V_T] \times [0,V_G]$, find measurable $u$ minimizing $\tau$ subject to $v_1(\tau) = V_T$ and $v_2(t) \le V_G$ on $[0,\tau]$. The pair is **pairwise feasible** if P1 is solvable for both labelings. Define

$$\gamma_1 = \frac{b_1 a_2}{b_2 a_1}.$$

**Proposition 1 (Case 1, $\gamma_1 > V_T/V_G$).** The time-optimal feedback control is

$$u^* = \begin{cases} U, & v_2 < V_G, \\ u_{arc} = \dfrac{a_2 V_G}{b_2}, & v_2 = V_G, \end{cases}$$

where $u_{arc}$ is the unique input keeping $v_2 \equiv V_G$. Optimal stimuli are full input until either $v_1 = V_T$ or the guard is reached, then the constant boundary input until $v_1 = V_T$; a solution exists from every initial state.

**Proposition 2 (Case 2, $\gamma_1 \le V_T/V_G$).** Along the guard, $v_1$ can no longer climb to $V_T$. When a solution exists it is bang/off/bang: $u^* = 0$ above a switching curve $\Gamma$ in $G$ and $u^* = U$ below it, so trajectories that would hit the guard first coast with no input down to $\Gamma$ and then receive full input until neuron 1 spikes. A time-optimal solution exists for all initial states iff $\Gamma$ meets the positive $v_2$-axis, i.e.

$$\Bigl(1 - \frac{a_1 V_T}{b_1 U}\Bigr)^{a_2} > \Bigl(1 - \frac{a_2 V_G}{b_2 U}\Bigr)^{a_1}.$$

**Lemma 1 (pairwise feasibility).** If neuron 1 is in Case 1 and neuron 2 is in Case 2 (for its own spike, with labels swapped), the pair is pairwise feasible iff

$$\Bigl(1 - \frac{a_2 V_T}{b_2 U}\Bigr)^{a_1} \ge \Bigl(1 - \frac{a_1 V_G}{b_1 U}\Bigr)^{a_2}.$$

If both neurons are in Case 2, pairwise feasibility is impossible unless $V_G = V_T$.

**Proposition 3 (non-existence for sequences).** For a pair satisfying the hypotheses of Lemma 1, time-optimal control of a spike sequence (problem P2, minimizing the total time to produce the prescribed order of spikes, each selective) has in general no solution when the sequence contains the subsequence "neuron 2, then neuron 1".

## Expansion

Without the state constraint the Hamiltonian $H = 1 + \lambda\cdot(Av + bu)$ has adjoints $\lambda_i(t) = c_i e^{a_i t}$, so the switching function $\lambda \cdot b$ changes sign at most once and optimal controls are bang-bang. In Case 1 the boundary arc is "uphill" for neuron 1: on $v_2 = V_G$ with $u = u_{arc}$, $\dot v_1 = -a_1 v_1 + b_1 a_2 V_G/b_2 > 0$ up to $v_1 = V_T$ exactly when $\gamma_1 V_G > V_T$, which gives Proposition 1, verified by a direct synthesis satisfying the Hamilton–Jacobi–Bellman equation. In Case 2 the arc stalls below threshold, so the only way to spike neuron 1 while respecting the guard is to let $v_2$ decay and then bang; the existence inequality is the condition that the zero-input flow from every state above $\Gamma$ reaches $\Gamma$. The value function is discontinuous along part of $\Gamma$ (loss of small-time local controllability), and in sequences ending "2 then 1" this discontinuity enters the terminal cost of the earlier spike, so the infimum of the total time is not attained.

## Depends on

- [First hit of the threshold under superthreshold drive](../../leaky-integrate-and-fire-neuron/lif-first-hit.md)

## Sources

- A. Nandi, H. Schättler, J. T. Ritt, S. Ching, "Fundamental Limits of Forced Asynchronous Spiking with Integrate and Fire Dynamics", Journal of Mathematical Neuroscience 7 (2017) 11, Problems P1–P2, Equations (6)–(17), (40)–(49), Propositions 1–3 and Lemma 1, <https://doi.org/10.1186/s13408-017-0053-5>, PMCID PMC5636789.
