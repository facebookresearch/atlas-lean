# Cell cycle clustering in the advancing and blocking threshold models

**Model.** Each of $N$ cells has a cell-cycle coordinate $x_i \in [0,1)$ (logarithmic volume between birth at $0$ and division at $1$, time normalized so the mean cycle length is $1$); at $x_i = 1$ the cell divides and the coordinate resets to $0$, and coordinates are read on the circle. A signaling region $S \subset [0,1)$ (a portion of S-phase) influences a preceding responsive region $R = [r, s]$ (a portion of G1) through a threshold $\tau$ on the fraction of cells in $S$:

$$
\frac{\mathrm{d}x_i}{\mathrm{d}t} = \begin{cases} 1 & x_i \notin R,\\ 1 + F(\#\{\text{cells in } S\}) & x_i \in R. \end{cases}
$$

- **Advancing model** (positive feedback, $F \to +\infty$ above threshold): whenever the fraction of cells in $S$ exceeds $\tau$, all cells in $R$ jump instantly to the start of $S$.
- **Blocking model** (negative feedback): while the fraction of cells in $S$ is at least $\tau$, cells reaching $s$ wait there; when the fraction drops below $\tau$, all waiting cells enter $S$ together.

Cells merged in either way stay synchronized forever and form a **cluster**; a cluster large enough to exceed $\tau$ by itself is **critical**.

**Theorem (advancing model).** Let $w$ be the initial distribution of cells.

- If $w$ exceeds the threshold on every interval of length $|S|$, except possibly inside $R$, the trajectory converges to a periodic orbit.
- If $w$ is below threshold on every interval of length $|S|$, it is an equilibrium (the profile simply rotates).
- Every other initial condition converges to an equilibrium with finitely many critical clusters separated by voids of length at least $|R| + |S|$.

Consequently at most $\lfloor (|R| + |S|)^{-1}\rfloor$ critical clusters can persist.

**Theorem (blocking model).** At most $\lceil |S|^{-1}\rceil$ critical clusters can persist. If the initial cell density everywhere exceeds twice the threshold, exactly $\lceil |S|^{-1}\rceil$ clusters form and persist.

**Theorem (robustness).** In the blocking model with small diffusive (random) perturbations of size $\epsilon < |S|/6$ and an initial density exceeding $2\tau + 2\epsilon$ everywhere, the system forms $\lfloor |S|^{-1}\rfloor$, $\lceil |S|^{-1}\rceil$ or $\lceil |S|^{-1}\rceil + 1$ critical clusters within one cell-cycle period, and they persist indefinitely.

## Expansion

In the advancing model, a critical cluster entering $S$ sweeps every cell in $R$ into itself, so it absorbs everything within distance $|R|$ behind it; it can coexist with another critical cluster only if the gap between them exceeds $|R| + |S|$, which bounds their number on the unit circle. In the blocking model, a critical cluster occupying $S$ holds back all cells arriving at $s$ for the time it spends in $S$, about $|S|$. Those cells are released together as the next cluster, so the circle is tiled by clusters spaced about $|S|$ apart. With dense initial data every released group is itself critical, giving exactly $\lceil 1/|S|\rceil$ clusters. Small noise blurs each cluster, but blocking resharpens it every cycle, so the cluster count changes by at most one. Clusters passing through S-phase at regular intervals produce oscillations in population oxygen consumption with period close to an integer divisor of the doubling time, as observed in yeast cultures, and smooth Hill-type feedback in simulations behaves like the idealized models.

## Sources

- Erik M. Boczko, Tomas Gedeon, Chris C. Stowers and Todd Young, "ODE, RDE and SDE Models of Cell Cycle Dynamics and Clustering in Yeast", arXiv (2008), Section 2 (general model, advancing and blocking models; Theorem 2.1, Corollary 2.2, Theorems 2.3 and 2.4), Section 3 (Theorem 3.1), <https://doi.org/10.48550/arXiv.0808.0723>.
