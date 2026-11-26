# Delay embedding and convergent cross mapping

**Delay vectors.** For a scalar time series $Z(t)$, an embedding dimension $E \ge 1$ and a lag $\tau > 0$, the delay vector is

$$\mathbf Z_E(t) = \big(Z(t), Z(t - \tau), \dots, Z(t - (E-1)\tau)\big) \in \mathbb R^E .$$

**Takens' theorem.** Let $\varphi$ be the time-$\tau$ map of a smooth flow on a compact $m$-dimensional manifold $M$ and $h : M \to \mathbb R$ a smooth observation. For generic $(\varphi, h)$ and $E \ge 2m + 1$, the delay map $\Phi(p) = \big(h(p), h(\varphi^{-1}(p)), \dots, h(\varphi^{-(E-1)}(p))\big)$ is an embedding of $M$ into $\mathbb R^E$, i.e. a diffeomorphism onto its image.

**Cross-mapping principle.** In a deterministic coupled system in which $Y$ drives $Z$ (the equation of $Z$ depends on $Y$), the attractor of the full system, and hence the current value $Y(t)$, is generically a continuous function of the delay vector $\mathbf Z_E(t)$ of the driven variable: there is a *continuous delay map* from the effect's delay space to the cause. If $Z$ does not depend, directly or indirectly, on $W$, no such map from $\mathbf Z_E$ to $W$ is guaranteed.

**Convergent cross mapping (CCM).** To test "$X$ causes $Y$", predict $X(T)$ from $\mathbf Y_E(T)$: find the $E + 1$ nearest neighbours of $\mathbf Y_E(T)$ among delay vectors in a library of length $L$, and average their contemporaneous $X$ values with weights decreasing exponentially in neighbour distance. The *cross-map skill* $\rho(L)$ is the Pearson correlation between actual and predicted $X$ over many $T$. CCM infers $X \to Y$ when $\rho(L) > 0$, $\rho(L)$ increases with $L$ (convergence), and $\rho$ exceeds its distribution under surrogate time series that preserve, for example, seasonality.

**Pathologies.**

- Strong unidirectional forcing can synchronise the driven variable to the driver, giving a continuous map in both directions and a spurious reverse inference.
- Process and measurement noise blur continuity; shared unobserved periodic drivers produce cross-map skill without direct causation.
- Symmetries can prevent the embedding guarantee (for example a variable whose equation is invariant under a sign change of another state).
- The prediction-lag refinement (choosing the lag at which cross-map skill peaks) can reject true links in some parameter regimes.

## Expansion

Because $\mathbf Z_E$ is generically an embedding of the full attractor, every state variable, including the driver $Y$, is a smooth function of $\mathbf Z_E$; nearest neighbours in $Z$-delay space are then mapped to nearby $Y$ values, and the nearest-neighbour estimate improves as the library fills the attractor more densely, which is the "convergent" part. A non-driving variable $W$ is not a function of the $Z$ attractor because $Z$'s dynamics carry no information about it. Granger causality instead asks whether adding the past of $X$ to an autoregressive model of $Y$ reduces prediction error; it presumes separability (information about $X$ is not already contained in $Y$'s past), which fails in exactly the deterministic coupled systems for which CCM is designed. Neither approach is a test of interventional causation.

## Sources

- A. E. Yuan, W. Shou, "Data-driven causal analysis of observational biological time series", eLife 11 (2022) e72518, sections on Granger causality and state space reconstruction (delay vectors and continuous delay maps, Figure 4; CCM procedure, Figure 6; pathologies from noise, shared drivers and synchrony, Figure 7; Appendix 4 on Takens' theorem and the prediction-lag test), <https://doi.org/10.7554/eLife.72518> (PMC9391047).
- G. Sugihara, R. May, H. Ye, C.-h. Hsieh, E. Deyle, M. Fogarty, S. Munch, "Detecting causality in complex ecosystems", Science 338 (2012) 496–500, <https://doi.org/10.1126/science.1227079>.
- F. Takens, "Detecting strange attractors in turbulence", Dynamical Systems and Turbulence, Lecture Notes in Mathematics 898 (1981) 366–381, <https://doi.org/10.1007/BFb0091924>.
