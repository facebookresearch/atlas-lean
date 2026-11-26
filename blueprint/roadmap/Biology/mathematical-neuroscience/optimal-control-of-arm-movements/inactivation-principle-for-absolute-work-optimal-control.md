# Inactivation principle for absolute-work optimal control

Consider a fully actuated mechanical system with $n$ degrees of freedom, $\ddot x = \phi(x, \dot x, u)$, with configuration $x$, net joint torques $u \in U$, $U$ a box with $0$ in its interior, $\phi$ smooth and $\partial \phi/\partial u$ invertible (for a limb, $\phi = M(x)^{-1}(u - \cdots)$ with inertia matrix $M$). With $X = (x, y) = (x, \dot x)$, a pointing movement of fixed duration $T$ goes from $(x_s, 0)$ to $(x_t, 0)$ and minimizes

$$J(u) = \int_0^T \Bigl(\dot A_w(X, u) + g(X, u)\Bigr)\, dt, \qquad \dot A_w = \sum_{i=1}^n |y_i u_i|,$$

the absolute work of the torques plus a smooth comfort term $g$ (for instance $\alpha |\ddot x|^2$). The total integrand is assumed strictly convex in $u$. A *partial inactivation* is a time interval of positive length on which some $u_i \equiv 0$; a *total inactivation* has all $u_i \equiv 0$ simultaneously. An extremal of Pontryagin's maximum principle with cost multiplier $\lambda < 0$ is *regular*.

1. **No abnormal extremals.** Since the system is feedback linearizable, every extremal with $\lambda = 0$ is bang (some control takes only boundary values), so optimal trajectories that are not bang are regular.
2. **Continuity.** Optimal controls along regular trajectories are continuous in $t$.
3. **Inactivation principle.** Along a regular optimal trajectory on which some control component $u_i^*$ changes sign at $t_c \in (0,T)$ while $y_i$ keeps a constant nonzero sign near $t_c$, there is partial inactivation: $u_i^* \equiv 0$ on an interval of positive length. If all regular extremals are continuous, then through any state with all $y_i \ne 0$ there pass extremals with total inactivation.
4. **Necessity of non-smoothness.** For an open dense set of smooth costs $\int_0^T f(X,u)\,dt$ (Whitney $C^\infty$ topology, with complement of arbitrarily large codimension), no minimizing control vanishes on a subinterval except along equilibria.

## Expansion

By strict convexity, maximizing the Hamiltonian $h = \lambda(\dot A_w + g) + \langle p, y\rangle + \langle q, \phi(x,y,u)\rangle$ over $u$ is equivalent to $0$ belonging to the generalized gradient in $u$. Because $|y_i u_i|$ has a kink at $u_i = 0$ with subdifferential $[-|y_i|, |y_i|]$, the condition $u_i^* = 0$ holds for an entire interval $I(t)$ of costate values, of width proportional to $|\lambda y_i| > 0$. This interval moves continuously with $t$. A sign change of $u_i^*$ forces the continuous costate expression to cross the whole of $I(t_c)$, which takes positive time, and during that time $u_i^* = 0$. Choosing the costate so that $0$ sits at the centre of the hypercube of such conditions gives total inactivation. Sign changes are needed for fast movements, which accelerate and then brake. Inactivation therefore appears automatically when $T$ is close to the minimum time, around the switching times of the bang–bang minimum-time control. With a smooth cost, transversality arguments show that constant optimal controls are only equilibria or bang arcs, so silent periods cannot occur generically. Simultaneous silence of agonist and antagonist muscles in fast arm movements is thus evidence for a non-smooth, work-like term in the cost.

## Sources

- B. Berret, C. Darlot, F. Jean, T. Pozzo, C. Papaxanthis, J.-P. Gauthier, "The inactivation principle: mathematical solutions minimizing the absolute work and biological implications for the planning of arm movements", *PLoS Computational Biology* (2008), Results (Eqs. (1)–(4), Definition 1, the Inactivation Principle) and Materials and Methods ("Nonexistence of abnormal trajectories", hypotheses $(H_1, H_2)$, Theorem 2, Lemma 1, Theorem 3), <https://doi.org/10.1371/journal.pcbi.1000194> (PMC2561290).
