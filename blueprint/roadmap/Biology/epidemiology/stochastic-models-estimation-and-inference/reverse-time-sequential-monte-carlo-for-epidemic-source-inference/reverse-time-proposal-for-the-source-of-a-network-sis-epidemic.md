# Reverse-time proposal for the source of a network SIS epidemic

On a finite graph $(V, E)$ each vertex is susceptible ($S$) or infected ($J$). Infected vertices recover at rate $\beta > 0$; a susceptible vertex $v$ is infected at rate $\alpha|N_v^J|$, where $N_v^J$ is its set of infected neighbors; and when no vertex is infected a new infection enters at rate $\gamma > 0$ at a uniformly chosen vertex. An infection is observed only when it first reaches $M$ infected vertices, at which moment the set of infected vertices is recorded. The source-inference target is the posterior law of the first infected vertex,

$$ \mathbb{E}_\mu\big[(\mathbf{1}_{\{v\}}(X_1))_{v\in V} \,\big|\, \tau_T < \tau_I\big] , $$

where $X_t$ is the set of infected vertices of the jump chain, $I = \{\varnothing\}$ and $T$ is the observed configuration.

A reverse-time proposal is obtained from an approximate conditional sampling distribution of one label given all others, based on the stationary law of a single vertex with frozen neighbors and a small $\varepsilon > 0$ allowing isolated infections in reverse time:

$$ \hat\pi\big(l(v) = J \mid \text{rest}\big) \propto \frac{\alpha|N_v^J| + \varepsilon}{\alpha|N_v^J| + \beta + \varepsilon}\, w(v), \qquad \hat\pi\big(l(v) = S \mid \text{rest}\big) \propto \frac{\beta}{\alpha|N_v^J| + \beta + \varepsilon} , $$

with a weight $w(v)$ (powers of $2$ on grid networks) favoring reverse-time infections that move toward the centroid of the infected set. Inserted into the Green's-function-ratio construction, this yields a reverse-time sequential Monte Carlo estimator of the source likelihood surface whose maximizers concentrate on one or two neighboring vertices near the true source on grids up to $100\times100$.

## Depends on

- [Green's function ratios as conditional sampling ratios](greens-function-ratios-as-conditional-sampling-ratios.md)

## Expansion

Forward simulation rarely reproduces the observed configuration because recoveries erase history and there is no natural reaction coordinate: the maximal infection size creates large outbreaks but does not favor the observed vertices. In reverse time the chain starts at the observed set and shrinks to the empty set, so the unknown origin is integrated over automatically. The single-vertex conditional law is exact if a vertex's neighbors were frozen, since its label then flips between rates $\alpha|N_v^J|$ and $\beta$; the $\varepsilon$ term is needed because in reverse time a vertex with no infected neighbors may become infected (a leaf of an infection that receded).

## Sources

- Jere Koskela, Dario Spanò, Paul A. Jenkins, "Inference and rare event simulation for stopped Markov processes via reverse-time sequential Monte Carlo", Statistics and Computing 28 (2018), 131–144, <https://doi.org/10.1007/s11222-017-9722-1>. Published version of arXiv:1603.02834, cited next; locators there refer to the arXiv version.
- J. Koskela, D. Spanò, P. A. Jenkins, "Inference and rare event simulation for stopped Markov processes via reverse-time sequential Monte Carlo", arXiv:1603.02834 (2016), Section 4.3 (the susceptible-infected-susceptible network; conditional sampling distribution, centre-of-mass weight, and the grid experiments). <https://doi.org/10.48550/arXiv.1603.02834>
