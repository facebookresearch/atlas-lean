# Kermack–McKendrick epidemic with dose-threshold resistance

**Definition.** A Kermack–McKendrick type epidemic with infectivity age and dose-threshold resistance has susceptibles satisfying $S'(t) = -S(t)I(t)$, where $I(t)$ is the force of infection, so $S(t) = S(0)e^{-J(t)}$ with cumulative force of infection $J(t) = \int_0^t I(s)\,ds$. Following Cooke's idea, each host has a resistance $m \ge 0$: a host infected at time $r$ becomes infective only at the time $t$ when the dose it has accumulated since infection reaches $m$, i.e. $\int_r^t I(s)\,ds = m$. Resistances are distributed across hosts by a probability measure $\nu$ on $[0,\infty)$: *fixed resistance* is $\nu = \delta_m$ with $m > 0$, and *distributed resistance* is $\nu(dm) = \sigma(m)\,dm$ with a continuous density $\sigma : \mathbb{R}_+ \to \mathbb{R}_+$. Infectives of infectivity age $a$ survive in the infective class with probability $P(a)$ (decreasing) and exert infectivity $\kappa(a)$ (essentially bounded). With $f(y) = 1 - e^{-y}$ and $[y]_+ = \max(y,0)$, the cumulative force of infection solves the Volterra-type equation

$$
J(t) = \int_0^t S(0) \int_{[0,\infty)} f\bigl([J(t-a) - m]_+\bigr)\,\nu(dm)\; P(a)\kappa(a)\,da + J_0(t),
$$

where $J_0$ is the (increasing) cumulative force of infection due to the initial infectives. Write $J_0^\infty = \lim_{t\to\infty} J_0(t)$, $J^\infty = \lim_{t\to\infty} J(t)$, $S^\infty = S(0)e^{-J^\infty}$, and $\mathcal{R}_0 = S(0)\int_0^\infty P(a)\kappa(a)\,da$, the basic reproduction number without resistance.

## Expansion

Without resistance ($\nu = \delta_0$) this is the Kermack–McKendrick model with infectivity age. Resistance delays the onset of infectiousness until enough dose has accumulated, which makes the incidence a thresholded functional of the cumulative force of infection; averaging over $\nu$ smooths the threshold.

## Sources

- Joan Ponce and Horst R. Thieme, "A Kermack–McKendrick type epidemic model with double threshold phenomenon (and a possible application to Covid-19)", Journal of Mathematical Biology 92 (2026), 33, <https://doi.org/10.1007/s00285-026-02348-8>; numbering as in arXiv:2409.17278: Section 2 (the model for fixed resistance) and Section 4 (the model for distributed resistance).
