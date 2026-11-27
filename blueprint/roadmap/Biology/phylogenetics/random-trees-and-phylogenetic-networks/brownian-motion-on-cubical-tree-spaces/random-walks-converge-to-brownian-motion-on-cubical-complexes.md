# Convergence of random walks to Brownian motion on cubical complexes

**Setting.** A cubical complex $X$ is obtained by gluing unit cubes $I^k = [0,1]^k$ ($k \le n$, with at least one $n$-cube) along faces by isometries. Assume $X$ is locally finite and equip it with the length metric extending the Euclidean metric on each cube. Let $G_X$ be the bipartite graph whose vertices are the $n$-cubes and the $(n-1)$-cubes, with an edge when the $(n-1)$-cube is a face of the $n$-cube, and assume $G_X$ is connected. BHV tree space on $N$ leaves is such a complex: its internal part consists of $(2N-3)!!$ orthants $\mathbb R_{\ge 0}^{N-2}$, one per resolved rooted topology, glued along their boundaries, and filling each orthant with unit cubes makes it cubical.

**Brownian motion.** Fix $t_0 > 0$ and $x_0$ in the interior of an $n$-cube. The Brownian motion $\mathcal B_{x_0,t_0}$ on $X$ is the law on continuous paths $\eta : [0,t_0] \to X$ with $\eta(0) = x_0$ that is constructed by projecting paths onto $I^n$: within an $n$-cube the path moves as reflected Brownian motion on $I^n$ (independent coordinates, each a standard Brownian motion on $[0,1]$ reflected at $0$ and $1$), and at each crossing of a codimension-1 face it continues in an $n$-cube chosen uniformly at random among those sharing that face. Paths meeting codimension-2 faces have probability zero.

**Random walk.** With $m$ steps per unit of coordinate and $\epsilon = (3t_0/m)^{1/2} < 1$, perform $r = mn$ moves from $y_0 = x_0$. At each move pick a coordinate $k \in \{1,\dots,n\}$ of the current $n$-cube uniformly and an increment $\delta \sim U(-\epsilon,\epsilon)$ (variance $t_0/m$). If the new $k$-th coordinate $\ell^* = \xi_k(y) + \delta$ stays in $[0,1]$, move there; otherwise the walk hits the face $\xi_k = 0$ or $1$, chooses uniformly among the $n$-cubes sharing that face (including the current one), and enters it at the reflected coordinate $-\ell^*$ or $2 - \ell^*$. Let $\mathcal W^m_{x_0,t_0}$ be the law of the resulting (linearly interpolated) path.

**Theorem.** As $m \to \infty$,

$$\mathcal W^m_{x_0,t_0} \xrightarrow{\;w\;} \mathcal B_{x_0,t_0},$$

weak convergence of probability measures on the path space with the uniform metric $d_\infty(\eta_1,\eta_2) = \sup_{t \le t_0} d(\eta_1(t), \eta_2(t))$. In particular the endpoint distributions (transition kernels at time $t_0$) of the random walks converge to the Brownian transition kernel.

No curvature assumption on $X$ is needed; the result extends to polyhedral complexes in which every top-dimensional cell is isometric to one fixed polyhedron.

## Expansion

A path on $X$ that avoids codimension-2 faces is determined by its projection to $I^n$ together with the sequence of codimension-1 crossings, i.e. a non-repeating walk on $G_X$. The Brownian law on $X$ is therefore the reflected Brownian law on $I^n$ combined with independent uniform choices of the next $n$-cube at each crossing. The random walk has exactly the same structure: its projection to $I^n$ is a reflected random walk, which converges to reflected Brownian motion by Donsker's theorem, and its cube choices are uniform at each crossing. Convergence on $X$ follows by summing over walks on $G_X$ and showing that sets of paths approaching codimension-2 faces or making many crossings carry vanishing mass uniformly in $m$.

## Sources

- Tom M.W. Nye, "Random walks and Brownian motion on cubical complexes", Stochastic Processes and their Applications 130 (2020), 2185–2199, <https://doi.org/10.1016/j.spa.2019.06.013>. Published version of arXiv:1508.02906, cited next; locators there refer to the arXiv version.
- Tom M. W. Nye, "Convergence of random walks to Brownian motion on cubical complexes", arXiv (2015). Algorithm 1, Theorem 10, Section 5. <https://doi.org/10.48550/arXiv.1508.02906>
