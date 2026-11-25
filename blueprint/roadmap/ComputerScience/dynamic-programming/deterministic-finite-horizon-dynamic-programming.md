# Backward induction for deterministic finite-horizon control

Consider stages $t = 0, \dots, N - 1$, finite state sets, nonempty finite admissible action sets $A_t(s)$, deterministic transitions $s' = F_t(s, a)$, real costs $c_t(s, a)$ and terminal cost $g$. The values $V_N = g$ and $V_t(s) = \min_{a \in A_t(s)}(c_t(s, a) + V_{t+1}(F_t(s, a)))$ equal the minimum total cost $\sum_{t' \ge t}c_{t'}(s_{t'}, a_{t'}) + g(s_N)$ over admissible action sequences from state $s$ at stage $t$, and choosing a minimizing action at each stage gives an optimal sequence. Equivalently, $V_t(s)$ is the shortest-path distance from $(t, s)$ to a sink in the stage-indexed acyclic graph with an arc $(t, s) \to (t + 1, F_t(s, a))$ of length $c_t(s, a)$ for each admissible action and an arc $(N, s) \to$ sink of length $g(s)$ for each terminal state. If some admissible set may be empty, infeasibility must be represented explicitly rather than by a minimum over the empty set.

## Sources

- S. Ma, *Handout 4: Deterministic Systems and the Shortest Path Problem*, SEEM 3470, CUHK, 2014 (after Bertsekas, Dynamic Programming and Optimal Control, Vol. I, §§2.1–2.2), §2.1 and the DP recursion (1), <https://www1.se.cuhk.edu.hk/~seem3470/Handouts/4-sp_dp>
