# SIR structured coalescent likelihood for serially sampled genealogies

Let an epidemic in a closed population of known size $N$ follow the SIR Markov jump process for $X(t) = (S(t), I(t))$, with infection events $(S,I) \to (S-1, I+1)$ at rate $\beta(t) S I$ and removals $I \to I-1$ at rate $\gamma(t) I$. A genealogy $\mathbf{g}$ of pathogen sequences sampled at times $s_1 < \dots < s_m$ has coalescent times $c_1 < \dots < c_{n-1}$; let $l(t)$ be the number of lineages at time $t$. Under the structured-coalescent approximation for the SIR model the coalescent rate is

$$ \lambda(t) = \binom{l(t)}{2}\, \frac{2\beta(t) S(t)}{I(t)} . $$

Partition each inter-coalescent interval $[c_{k-1}, c_k)$ by the sampling times into subintervals $\mathcal{I}_{0,k}, \dots, \mathcal{I}_{i_k-1,k}$ with constant lineage counts $l_{i,k}$. With $X$ and $\theta = (\beta, \gamma)$ piecewise constant on a time grid, the genealogy density is

$$ \Pr(\mathbf{g} \mid X, \theta) \propto \prod_{k=2}^{n} \binom{l(c_{k-1})}{2}\frac{2\beta(c_{k-1})S(c_{k-1})}{I(c_{k-1})}\, \exp\Big(-\sum_{i=0}^{i_k - 1} \int_{\mathcal{I}_{i,k}} \binom{l_{i,k}}{2}\frac{2\beta(u)S(u)}{I(u)}\, du\Big) , $$

an inhomogeneous pure-death likelihood whose integrals are available in closed form. When $S(t) \approx N$ and $\beta$ is constant it reduces to Kingman's coalescent with effective population size $I(t)/(2\beta N)$.

## Expansion

Coalescences happen only through infection events, which join two lineages when both the infector and the infectee are ancestral; with $l$ lineages among $I$ infecteds this has probability about $\binom{l}{2}/\binom{I}{2}$ per infection, and multiplying by the incidence $\beta S I$ gives the rate. Sampling events add lineages and censor waiting times, which is why each inter-coalescent interval is split at sampling times. Only coalescent times carry information about the dynamics in this likelihood; sampling times are treated as fixed.

## Sources

- Mingwei Tang, Gytis Dudas, Trevor Bedford, Vladimir N. Minin, "Fitting stochastic epidemic models to gene genealogies using linear noise approximation", The Annals of Applied Statistics 17 (2023), 1–22, <https://doi.org/10.1214/21-aoas1583>. Published version of arXiv:1902.08877, cited next; locators there refer to the arXiv version.
- M. Tang, G. Dudas, T. Bedford, V. N. Minin, "Fitting stochastic epidemic models to gene genealogies using linear noise approximation", arXiv:1902.08877 (2019), Section 2.1 (genealogy as data; coalescent rate and the structured coalescent likelihood for serially sampled genealogies). <https://doi.org/10.48550/arXiv.1902.08877>
