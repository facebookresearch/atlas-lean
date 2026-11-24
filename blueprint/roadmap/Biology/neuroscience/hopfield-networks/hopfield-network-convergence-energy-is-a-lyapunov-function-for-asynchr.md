# Convergence of asynchronous Hopfield networks

Hopfield (1982) considers $N$ neurons with states $V_i \in \{0, 1\}$ and connection strengths $T_{ij}$ ($T_{ij} = 0$ for unconnected pairs). Each neuron $i$ readjusts its state at random times, asynchronously, setting $V_i = 1$ if $\sum_{j \ne i} T_{ij}V_j > U_i$ and $V_i = 0$ if $\sum_{j \ne i} T_{ij}V_j < U_i$, with thresholds $U_i = 0$ unless otherwise stated. For symmetric weights $T_{ij} = T_{ji}$ he defines the energy

$$E = -\tfrac12 \sum_{i \ne j} T_{ij} V_i V_j \qquad \text{(Eq. 7)},$$

shows that a change $\Delta V_i$ changes it by $\Delta E = -\Delta V_i \sum_{j \ne i} T_{ij}V_j$ (Eq. 8), and concludes that the update rule makes $E$ monotonically decreasing, so that state changes continue until a (local) minimum of $E$ is reached. Explicitly: if neuron $i$ changes from $0$ to $1$ then $\sum_{j\ne i}T_{ij}V_j > 0$ and $\Delta E < 0$, and if it changes from $1$ to $0$ then the sum is negative and again $\Delta E < 0$; since $E$ takes finitely many values on $\{0, 1\}^N$, every update sequence (with the convention that a neuron whose input equals the threshold keeps its state) contains only finitely many state changes, so the state is eventually constant. The eventual state is a fixed point of every single-neuron update provided every neuron is updated infinitely often.

## Expansion

1. The model: binary states, symmetric weights, the single-neuron update rule with its tie convention, and update schedules, deterministic and random.
2. The identity (8) for $\Delta E$ and strict decrease on every change of state.
3. Finiteness of the number of changes along any schedule and eventual constancy; the bound $2^N - 1$ on the number of strict changes, as a separate statement.
4. Stability of the limit under the fairness hypothesis, and almost-sure fairness of i.i.d. schedules in which every neuron has positive probability (second Borel–Cantelli lemma).
5. Without symmetry the energy argument fails; the source's simulations with asymmetric $T_{ij}$, and the [capacity of the Hopfield associative memory](../../../Biology/neuroscience/hopfield-networks/mceliece-posner-rodemich-venkatesh-capacity-of-the-hopfield-associativ.md), are separate topics.

## Sources

- J. J. Hopfield, Neural networks and physical systems with emergent collective computational abilities, Proc. Natl. Acad. Sci. USA 79 (1982), 2554–2558, update rule and Eqs. (7)–(8). <https://doi.org/10.1073/pnas.79.8.2554>
