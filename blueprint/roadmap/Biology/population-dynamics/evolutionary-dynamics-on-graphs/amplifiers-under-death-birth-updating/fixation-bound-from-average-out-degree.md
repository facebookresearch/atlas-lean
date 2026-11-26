# Fixation bound from the average out-degree

Let $G_N$ be a strongly connected population structure on $N$ vertices, given by nonnegative edge
weights $w_{uv}$ with no self-loops (edges may be directed and the weights need not be symmetric),
and let $d$ be the average out-degree of $G_N$. Consider the **death-Birth Moran process**: at each
step a vertex is chosen uniformly at random to die, and one of its neighbours $u$ is chosen to fill
the vacancy with probability proportional to $w_{uv} f(u)$, where the fitness $f$ equals $r$ on
mutant vertices and $1$ on resident vertices. Write $\rho_{\mathrm{dB}}(G_N, r)$ for the probability
that a single mutant of fitness $r$, placed at a uniformly random vertex, reaches fixation. Then for
every $r > 1$

$$\rho_{\mathrm{dB}}(G_N, r) \ \le\ \frac{d\,r}{d\,r + d + r - 1}.$$

In particular the bound is uniform in $r$: letting $r \to \infty$ it gives
$\rho_{\mathrm{dB}}(G_N, r) \le d/(d+1) < 1$ for every fixed $d$.

## Proof sketch

The intuition is a one-step extinction event. If the vertex $v$ hosting the initial mutant is
selected for death before any of its $d$ neighbours is selected, the mutant lineage is lost at once,
whatever the value of $r$; for an unweighted $d$-regular graph this event has probability
$1/(d+1)$, giving $\rho_{\mathrm{dB}} \le d/(d+1)$. The displayed bound is the refinement of this
argument that also covers weighted, directed and irregular structures, in which the mutant may
survive the first death only by being reproduced into the vacancy, an event whose probability is
controlled by $r$ and the out-degree.

## Sources

- J. Tkadlec, A. Pavlogiannis, K. Chatterjee, M. A. Nowak, "Limits on amplifiers of natural selection under
  death-Birth updating", PLoS Computational Biology 16 (2020) e1007494, Lemma 1,
  <https://doi.org/10.1371/journal.pcbi.1007494> (PMC6968837).
