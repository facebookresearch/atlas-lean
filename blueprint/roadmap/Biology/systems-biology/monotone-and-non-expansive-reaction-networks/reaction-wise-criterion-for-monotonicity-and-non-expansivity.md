# Reaction-wise criterion for monotonicity and non-expansivity

**Setting.** A non-catalytic reaction network on $n$ species has stoichiometric matrix $\Gamma = [\Gamma_1, \dots, \Gamma_m]$, each column a reaction vector labeled reversible or irreversible, and dynamics $\dot x = \Gamma R(x)$ on $\mathbb{R}^n_{\ge 0}$, where each rate $R_i$ is $C^1$ and obeys *general kinetics*: a rate strictly increases in each of its reactant concentrations (and, for a reversible reaction, strictly decreases in each product concentration), depends on no other species, and cannot consume an absent species. A closed, pointed, convex cone $K$ orders $\mathbb{R}^n$ by $x \le_K y \iff y - x \in K$; the network is **monotone with respect to $K$** if, for every choice of general kinetics, the flow $\phi_t$ satisfies $x \le_K y \Rightarrow \phi_t(x) \le_K \phi_t(y)$ for all $t \ge 0$. It is **non-expansive** for a norm $|\cdot|$ if $|\phi_t(x) - \phi_t(y)| \le |x - y|$ for all $t \ge 0$ and every choice of general kinetics.

**Sign regions.** For a reaction vector $v$ let $Q_1(v) = \{x : x_j v_j \ge 0 \text{ for all } j\}$ if the reaction is reversible, and $Q_1(v) = \{x : x_j v_j \ge 0 \text{ whenever } v_j < 0\}$ if it is irreversible; put $Q_1^{+}(v) = Q_1(v) \setminus Q_1(-v)$ and $Q_1^{-}(v) = Q_1(-v) \setminus Q_1(v)$.

**Statement.**

1. (Decomposition.) The network is monotone with respect to $K$ if and only if each single-reaction network $\dot x = \Gamma_i R_i(x)$ is monotone with respect to $K$.
2. (Closure operations.) Given $v$ and a reaction $\Gamma_i$, define the operations: if $v \in Q_1^{+}(\Gamma_i)$, produce $v - \alpha \Gamma_i$ with $\alpha > 0$ minimal such that $v - \alpha\Gamma_i \in Q_1(-\Gamma_i)$; if $v \in Q_1^{-}(\Gamma_i)$, produce $v + \alpha\Gamma_i$ with $\alpha > 0$ minimal such that $v + \alpha \Gamma_i \in Q_1(\Gamma_i)$; if $v \notin Q_1(\Gamma_i) \cup Q_1(-\Gamma_i)$, produce both $v + \alpha_1 \Gamma_i \in Q_1(\Gamma_i)$ and $v - \alpha_2\Gamma_i \in Q_1(-\Gamma_i)$ with $\alpha_1, \alpha_2 > 0$ minimal. Then the network is monotone with respect to $K$ if and only if $K$ is closed under these operations for every reaction, and it is non-expansive with respect to a norm with unit ball $B$ if and only if $B$ is closed under the same operations.

Consequently a candidate cone or unit ball can be generated from one starting vector by repeatedly applying the operations; for polyhedral $K$ it suffices to check the extreme rays.

## Expansion

Monotonicity of $\dot x = f(x)$ with respect to $K$ is equivalent to the Walcher boundary condition $k_2^\top J_f(x) k_1 \ge 0$ for all $k_1 \in \partial K$, $k_2 \in K^*$ with $k_2^\top k_1 = 0$. Under general kinetics the Jacobian is $\Gamma\,\partial R(x) = \sum_i \Gamma_i \nabla R_i(x)^\top$, and since the sign pattern of each $\nabla R_i$ is fixed but its magnitudes are free, the boundary condition must hold for each summand separately, giving part 1. For one reaction the condition says that pushing a vector of $K$ along $\pm\Gamma_i$ until it reaches the sign region where the rate change opposes the push stays inside $K$; this is exactly closure under the three operations. The same argument applied to the faces of a unit ball gives the non-expansivity statement.

## Sources

- A. Duvall, Computationally checking if a reaction network is monotone or non-expansive, arXiv (2024). <https://doi.org/10.48550/arXiv.2409.12487> (Lemma 2, Lemma 9, Theorem 2; background Theorem 1.)
