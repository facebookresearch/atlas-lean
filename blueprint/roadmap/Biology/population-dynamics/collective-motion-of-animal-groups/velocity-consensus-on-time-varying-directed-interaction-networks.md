# Velocity consensus on time-varying directed interaction networks

**Setting.** A group of $n$ animals $a_1,\dots,a_n$ has velocities $v_i(t)\in\mathbb R^m$. Each individual adjusts its velocity towards those of its current neighbours $N(t,a_i)$ (for example its nearest topological neighbours), which define a time-varying directed interaction graph $\mathbb G(t)$ on $\{a_1,\dots,a_n\}$. A **velocity coordination system** is
$$\dot v_i(t)=-\sum_{a_j\in N(t,a_i)}g_{ij}\bigl(\|v_i-v_j\|\bigr)\frac{v_i-v_j}{\|v_i-v_j\|},\qquad g_{ij}(0)=0,\quad g_{ij}(r)>0\ (r>0).$$
For each directed edge let $\ell_{ij}=\int_0^\infty\mathbf 1\{(a_i,a_j)\text{ active at }t\}\,dt$ be its total active time; the **$\infty$-adjoint graph** $\mathbb G_\infty$ keeps exactly the edges with $\ell_{ij}=\infty$. $\mathbb G(t)$ is a *stationary time-varying network* if every edge of $\mathbb G_\infty$ has active intervals whose lengths do not shrink to $0$ and inactive gaps whose lengths stay bounded. A strongly connected component of a directed graph is *independent* if no directed path enters it from outside; *consensus* means $v_i(t)-v_j(t)\to0$ for all $i,j$.

**Theorem 5.2 and Corollaries 5.3-5.4 (non-expanding hull).** The convex hull $\Xi(t)$ of the velocity set $\{v_1(t),\dots,v_n(t)\}$ is non-increasing: $\Xi(t+\delta t)\subseteq\Xi(t)$ for all $t\ge0$, $\delta t>0$. Hence the system is Lyapunov stable and $\Xi(\infty)=\lim_{t\to\infty}\Xi(t)$ exists.

**Theorem 5.10 (consensus criterion).** If $\mathbb G(t)$ is a stationary time-varying network, all individuals reach velocity consensus (for every initial condition) if and only if $\mathbb G_\infty$ has exactly one independent strongly connected component. The "only if" part holds without stationarity (Theorem 5.9).

## Expansion

Each velocity moves in the direction of a nonnegative combination of vectors pointing to its neighbours' velocities, so no velocity can leave the current convex hull and, by projecting onto coordinate axes (Proposition 5.1), extreme coordinates cannot increase. Interactions active only for finite total time have finite cumulative effect, so asymptotically only $\mathbb G_\infty$ matters. An independent component receives no influence from outside, so two independent components keep their own limiting velocities and consensus fails; with a single independent component, its members reach a common velocity because they interact infinitely often with gaps bounded by stationarity, and every other individual is reachable from it along edges of $\mathbb G_\infty$ and is pulled to the same value. Biologically, the consensus velocity is inherited from the leading independent subgroup, and large moving groups form by merging pre-existing subgroups rather than by gradual accretion of individuals.

## Sources

- J. Jin, "A theoretical framework for the formation of large animal groups: topological coordination, subgroup merging, and velocity inheritance", arXiv preprint (2025), Proposition 5.1, Theorem 5.2, Corollaries 5.3 and 5.4, Theorems 5.8-5.10, <https://doi.org/10.48550/arXiv.2512.00467>.
