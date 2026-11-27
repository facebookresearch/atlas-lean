# Shape theorem for the spatial death-birth Moran model

**Model ($\mathrm{DB}^{\mathrm f}$).** On $\mathbb Z^d$ each cell dies at rate $1$ and is replaced by the offspring of a neighbour chosen with probability proportional to fitness ($1$ for residents, $\lambda = 1 + \beta > 1$ for mutants). Let $\xi^0_t$ be the set of mutant sites at time $t$, started from a single mutant at the origin, and $\tau_\varnothing$ its extinction time; by the survival bounds, $\mathbb P(\tau_\varnothing = \infty) > 0$ for every $\beta > 0$ and $d \ge 1$.

**Theorem ($d \ge 2$).** There is a convex set $D \subset \mathbb R^d$ such that for every $\varepsilon > 0$,

$$\mathbb P\Bigl(\exists\, t_* < \infty : (1-\varepsilon)\, tD \cap \mathbb Z^d \subseteq \xi^0_t \subseteq (1+\varepsilon)\, tD \ \text{ for all } t \ge t_* \ \Big|\ \tau_\varnothing = \infty\Bigr) = 1.$$

On the way, there are constants $c, A, \alpha, z_0 > 0$ such that, with $D_r$ the Euclidean ball of radius $r$,

$$\mathbb P\bigl(D_{ct} \subseteq \xi^0_{t + z^2} \text{ for all } t \ge 0 \,\big|\, \tau_\varnothing = \infty\bigr) \ge 1 - A e^{-\alpha z}, \qquad z \ge z_0,$$

and large mutant sets rarely die: $\sup_{|A| = k} \mathbb P(\tau^A_\varnothing < \infty) \le C e^{-\gamma k^{(d-1)/d}}$.

**One dimension.** On $\mathbb Z$ the shape is explicit: conditioned on survival, the mutant interval grows linearly with $D = [-c_1(\beta), c_1(\beta)]$, $c_1(\beta) = \beta/(2+\beta)$, the long-run net drift of each endpoint.

**Related updating rules.** A death-birth model in which fitness lowers the death rate instead ($\mathrm D^{\mathrm f}\mathrm B$: mutants die at rate $1/\lambda$, replacement by a uniform neighbour) is a time change of the biased voter model ($\mathrm B^{\mathrm f}\mathrm D$), so both obey the Bramson-Griffeath shape theorem. When fitness acts only on the second event of the update ($\mathrm{DB}^{\mathrm f}$ or $\mathrm{BD}^{\mathrm f}$), zero-bias mutant-resident edges appear, and the $\mathrm{BD}^{\mathrm f}$ model is not even additive.

## Depends on

- [Survival probability of an advantageous mutant in the spatial death-birth Moran model](survival-probability-of-an-advantageous-mutant-in-the-spatial-death-birth-moran-model.md)

## Proof sketch

The $\mathrm{DB}^{\mathrm f}$ process is additive, translation invariant and strong Markov, and has a graphical construction with a dual set-valued process in which a site may be linked to a random subset of its neighbours. Inside this dual one embeds a walk that, after a time change by $(1+\lambda)/2$, moves toward the origin at rate $\lambda/(2d)$ and away at rate $1/(2d)$, exactly the walk Bramson and Griffeath used for the biased voter model; this gives the linearly expanding ball with exponential tail. The decay of extinction probabilities for large sets (from the isoperimetric drift bound) and the fact that the process cannot linger at sizes $o(t^{d/(d+1)})$ supply the regularity needed for a subadditive argument, which yields a convex limit shape. In one dimension the conditioned edge drifts are explicit and converge to $(\lambda-1)/(\lambda+1)$.

## Sources

- Jasmine Foo, Einar Bjarki Gunnarsson, Kevin Leder and David Sivakoff, "Dynamics of Advantageous Mutant Spread in Spatial Death-Birth and Birth-Death Moran Models", *Communications on Applied Mathematics and Computation* 6 (2024), 576–604, <https://doi.org/10.1007/s42967-023-00278-6>. Preprint version: arXiv:2209.11852 (2022), Section 4.4, Proposition 7.1, Lemmas 7.2 and 7.3, Proposition 7.4, and Section 8, <https://doi.org/10.48550/arXiv.2209.11852>.
