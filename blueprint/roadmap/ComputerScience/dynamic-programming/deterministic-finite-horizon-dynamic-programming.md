# Backward induction for deterministic finite-horizon control

Consider stages $t = 0, \dots, N - 1$, a set $S$ of states and a set $U$ of actions, nonempty finite admissible action sets $A_t(s) \subseteq U$ for $t < N$ and $s \in S$, deterministic transitions $s' = F_t(s, a)$, real costs $c_t(s, a)$ and a real terminal cost $g$ on $S$. The same state set $S$ serves at every stage, and it need not be finite: only the admissible sets must be finite and nonempty. Let $V : \{0, \dots, N\} \times S \to \mathbb{R}$ satisfy $V_N = g$ and

$$
V_t(s) = \min_{a \in A_t(s)} \bigl(c_t(s, a) + V_{t+1}(F_t(s, a))\bigr) \qquad (t < N,\ s \in S).
$$

An admissible sequence from state $s$ at stage $t \le N$ consists of states $s_t, \dots, s_N$ and actions $a_t, \dots, a_{N-1}$ with $s_t = s$, $a_{t'} \in A_{t'}(s_{t'})$ and $s_{t'+1} = F_{t'}(s_{t'}, a_{t'})$ for $t \le t' < N$; its total cost is $\sum_{t \le t' < N} c_{t'}(s_{t'}, a_{t'}) + g(s_N)$. Then, for every stage $t \le N$ and state $s$:

1. $V_t(s)$ is the minimum total cost of an admissible sequence from $s$ at stage $t$, and some admissible sequence attains it.
2. Choosing a minimizing action at each stage gives an optimal sequence: an admissible sequence from $s$ at stage $t$ in which each action $a_{t'}$, for $t \le t' < N$, minimizes $c_{t'}(s_{t'}, a) + V_{t'+1}(F_{t'}(s_{t'}, a))$ over $a \in A_{t'}(s_{t'})$ has total cost $V_t(s)$.
3. Equivalently, $V_t(s)$ is the shortest-path distance from $(t, s)$ to the sink in the stage-indexed graph: the least length of a path from $(t, s)$ to the sink, which exists. The vertices of this graph are the pairs $(t', s')$ with $t' \le N$ and $s' \in S$, and a sink; it has an arc $(t', s') \to (t' + 1, F_{t'}(s', a))$ of length $c_{t'}(s', a)$ for each $t' < N$ and each admissible action $a \in A_{t'}(s')$, so two actions with the same successor give parallel arcs, and an arc $(N, s') \to$ sink of length $g(s')$ for each state $s'$. The length of a path is the sum of the lengths of its arcs.

The admissible sets are nonempty and finite so that every minimum exists. The statement does not cover empty admissible sets: there infeasibility must be represented explicitly rather than by a minimum over the empty set.

## Sources

- S. Ma, *Handout 4: Deterministic Systems and the Shortest Path Problem*, SEEM 3470, CUHK, 2014 (its suggested reading: D. P. Bertsekas, *Dynamic Programming and Optimal Control*, Vol. I, 3rd ed., Athena Scientific, 2005, §§2.1–2.2), §2.1 and the DP recursion (1); cf. the worked example in §2.2, which reads an optimal path off the analogous recursion (3), <https://www1.se.cuhk.edu.hk/~seem3470/Handouts/4-sp_dp>
- D. P. Bertsekas, *Lecture Slides – Dynamic Programming*, based on lectures given at MIT, Fall 2015: Lecture 2, slide "DP algorithm" (PDF p. 20), which states for the general finite-horizon problem, of which the deterministic problem is a special case, that a policy choosing a minimizing control for each state and stage is optimal; Lecture 3, slides "Deterministic finite-state problem" and "Backward and forward DP algorithms" (PDF pp. 25–26), which identify controls with arcs and the optimal cost with the length of a shortest path, <https://web.mit.edu/people/dimitrib/DP_Slides_2015.pdf>
