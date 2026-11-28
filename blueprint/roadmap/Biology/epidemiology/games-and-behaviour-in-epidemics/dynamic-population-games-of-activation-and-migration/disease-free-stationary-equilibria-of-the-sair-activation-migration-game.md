# Disease-free stationary equilibria of the SAIR activation–migration game

**Game.** Agents have infection states $s \in \{\mathtt S, \mathtt A, \mathtt I, \mathtt R, \mathtt U\}$ (susceptible, asymptomatic infected, symptomatic infected, knowingly recovered, unknowingly recovered; $\mathtt R$ and $\mathtt U$ are immune) and zones $z \in \{1,\dots,Z\}$. Each day an agent in $(s,z)$ chooses an activation degree $a \in \{0,1,\dots,a_{\max}\}$ (number of contacts) and a destination zone $\tilde z$. A policy $\pi[a,\tilde z \mid s,z]$ (common to all agents, identical for $\mathtt S, \mathtt A, \mathtt U$ who have never shown symptoms) and the state distribution $d$ form the social state $(\pi,d)$, which induces a Markov transition matrix $P(\pi,d)$ through infection by random contacts among activated agents. Immediate rewards are

$$r[s,z,a,\tilde z] = r_{\rm act}[s,z,a] - c_{\rm mig}\mathbf 1_{\{\tilde z \ne z\}} - c_{\rm dis}\mathbf 1_{\{s = \mathtt I\}}, \qquad r_{\rm act}[s,z,a] = o[a] - c[s,z,a],$$

with social benefit $o$ non-decreasing, $o[0] = 0$, and lockdown costs $c$ non-decreasing in $a$ and ordered $c[\mathtt I,\cdot] \ge c[\mathtt S,\cdot] = c[\mathtt A,\cdot] = c[\mathtt U,\cdot] \ge c[\mathtt R,\cdot]$. Agents maximize expected discounted reward with discount factor $\alpha \in (0,1)$, giving state-action values $Qs,z,a,\tilde z$ and best responses $B_{s,z}(\pi,d)$. A **stationary equilibrium** is $(\pi^*,d^*)$ with $\pi^*[\cdot \mid s,z] \in B_{s,z}(\pi^*,d^*)$ for all $(s,z)$ and $d^* = d^*P(\pi^*,d^*)$. A stationary equilibrium always exists.

**Proposition.** Let $r^*_{\rm act}[s,z] = \max_a r_{\rm act}[s,z,a]$ with maximizers $\mathcal A^*_{s,z}$, $\bar r_{\rm act}[s] = \max_z r^*_{\rm act}[s,z]$, $\bar{\mathcal Z}_s = \arg\max_z r^*_{\rm act}[s,z]$, and

$$\mathcal Z^0_s = \Big\{z : \bar r_{\rm act}[s] - r^*_{\rm act}[s,z] > \frac{1-\alpha}{\alpha}\,c_{\rm mig}\Big\}.$$

Assume the transition rate from unknowingly to knowingly recovered is positive and $\alpha, c_{\rm mig} > 0$. Then every social state $(\pi^*,d^*)$ such that

- $d^*[\mathtt A,z] = d^*[\mathtt I,z] = d^*[\mathtt U,z] = 0$ for all $z$ (no infection, all unaware recoveries resolved),
- $d^*[s,z] = 0$ for $z \in \mathcal Z^0_s$,
- agents only use activation levels in $\mathcal A^*_{s,z}$,
- agents in a zone of $\mathcal Z^0_s$ migrate to a zone in $\bar{\mathcal Z}_s$, and agents in other zones stay,

is a stationary equilibrium. So disease-free equilibria are computed without solving a fixed point: activation is myopically optimal, and agents leave exactly those zones whose activation reward deficit exceeds the amortized migration cost $\frac{1-\alpha}{\alpha}c_{\rm mig}$.

## Expansion

With no infected agents, infection probabilities vanish and the value of each state decouples into immediate activation reward plus continuation. Staying forever in zone $z$ is worth $r^*_{\rm act}[s,z]/(1-\alpha)$, while paying $c_{\rm mig}$ once and moving to a best zone yields $-c_{\rm mig} + \alpha\,\bar r_{\rm act}[s]/(1-\alpha)$ plus today's reward; comparing gives the threshold defining $\mathcal Z^0_s$. Stationarity of $d^*$ holds because nobody remains in zones of $\mathcal Z^0_s$ and the infection states are absorbing in the disease-free set. Existence of stationary equilibria in general is the existence theorem for dynamic population games, a fixed-point argument on the compact convex set of social states.

## Sources

- Ezzat Elokda, Saverio Bolognani, Ashish R. Hota, "A Dynamic Population Model of Strategic Interaction and Migration under Epidemic Risk", in 2021 60th IEEE Conference on Decision and Control (CDC) (2021), 2085–2091, <https://doi.org/10.1109/cdc45484.2021.9683739>. Published version of arXiv:2109.03182, cited next; locators there refer to the arXiv version.
- Ezzat Elokda, Saverio Bolognani, Ashish R. Hota, "A Dynamic Population Model of Strategic Interaction and Migration under Epidemic Risk", arXiv (2021). Model section, stationary equilibrium definition and existence theorem, Proposition on the characterization of equilibria. <https://doi.org/10.48550/arXiv.2109.03182>
