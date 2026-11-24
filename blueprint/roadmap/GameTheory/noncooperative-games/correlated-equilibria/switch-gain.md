# Gain from a switched recommendation

In a finite game with costs $c_i$, the gain of player $i$ at the profile $s$ from playing $k$
whenever it is told to play $j$ is

$$g_i^{j\to k}(s) = \begin{cases} c_i(s) - c_i(k, s_{-i}) & \text{if } s_i = j, \\ 0 & \text{otherwise.}\end{cases}$$

With payoffs $u_i = -c_i$ this is the bracket $u_i(k, s_{-i}) - u_i(s)$ of the correlated
equilibrium inequalities, restricted to the event $\{s_i = j\}$.

## Sources

- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, §2, Definition, and (2.1a).
