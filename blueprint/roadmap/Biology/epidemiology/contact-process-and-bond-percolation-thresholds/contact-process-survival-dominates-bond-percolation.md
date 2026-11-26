# Contact process survival dominates bond percolation

**Setting.** Let $G$ be an infinite, locally finite, connected graph with root $o$.
- *Bond percolation:* each edge is open independently with probability $p$; $\theta_{\mathrm{bond}}(p) = P_p(|\mathcal C(o)| = \infty)$ and $p_c(G) = \inf\{p : \theta_{\mathrm{bond}}(p) > 0\}$. Bond percolation is the cluster structure of an SIR epidemic in which each infective transmits to each neighbour once with probability $p$.
- *Contact process:* each infected vertex recovers at rate $1$ and infects each neighbour at rate $\lambda$ (an SIS epidemic with reinfection); $\theta_{\mathrm{CP}}(\lambda)$ is the probability that the process started from $\{o\}$ survives forever, and $\lambda_c(G) = \inf\{\lambda : \theta_{\mathrm{CP}}(\lambda) > 0\}$.

**Theorem.** If $0 < p \le 1/2$ and $\lambda \ge 20p$, then

$$\theta_{\mathrm{CP}}(\lambda) \ge \tfrac34\,\theta_{\mathrm{bond}}(p).$$

**Corollary.** If $p_c(G) < 1/2$ then $\lambda_c(G) \le 20\,p_c(G)$. In particular $p_c(G) = 0$ implies $\lambda_c(G) = 0$: on any graph where SIR-type percolation occurs at every positive transmission probability, the SIS contact process survives at every positive infection rate.

**Trees.** For an infinite, locally finite tree $T$ with $p_c(T) < 1$, $\lambda_c(T) \le p_c(T)/(1 - p_c(T)) = 1/(\mathrm{br}(T) - 1)$, where $\mathrm{br}$ is the branching number.

**Contrast with SIR.** There is a graph $G_{\mathrm{chain}}$ with $p_c(G_{\mathrm{chain}}) = 0$ and $\lambda_c(G_{\mathrm{chain}}) = 0$, yet on which the continuous-time SIR epidemic infects only finitely many vertices almost surely for every $\lambda > 0$: reinfection, not the transmission probability alone, is what lets the contact process exploit percolation clusters.

## Expansion

The key finite statement: for a finite graph $H$, a target set $B$ and $o \notin B$, the contact process from $o$ reaches $B$ with probability at least $\tfrac34 P_p(o \leftrightarrow B)$ when $\lambda \ge 20p$. It is proved with a submartingale built from percolation clusters: weight the current infected set $A$ by $4^{-\mathcal N}$, with $\mathcal N$ the number of infected vertices in the open cluster of $B$, and use the boundary inequality $E_p[\mathcal N 4^{-\mathcal N}] \le 5p\,E_p[\mathcal M 4^{-\mathcal N}]$, where $\mathcal M$ counts edges from $A$ into the cluster. When $\lambda \ge 20p$, new infections along such edges outpace recoveries in expectation. Exhausting $G$ by balls gives the theorem. On trees a direct generation-by-generation comparison yields the sharper constant.

## Sources

- Benedikt Jahnel, Lukas Lüchtrath and Christian Mönch, "Vanishing bond-percolation threshold implies vanishing contact-process threshold", arXiv:2611.27354 (2026), comparison theorem and corollary, tree proposition, chain-graph proposition and boundary lemma, <https://doi.org/10.48550/arXiv.2611.27354>.
