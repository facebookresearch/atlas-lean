# The Hohmann transfer minimizes two-impulse delta-v

Let $\mu > 0$ be the gravitational parameter, and let $0 < r_1 < r_2$ be the radii of two coplanar circular orbits. The *Hohmann transfer* applies a tangential impulse at radius $r_1$, coasts half an orbit along the ellipse with periapsis $r_1$ and apoapsis $r_2$, and then applies a second tangential impulse at $r_2$.

**Theorem.**
1. The Hohmann transfer has total velocity change

    $$
    \Delta v_H = \sqrt{\frac{\mu}{r_1}}\left(\sqrt{\frac{2r_2}{r_1 + r_2}} - 1\right) + \sqrt{\frac{\mu}{r_2}}\left(1 - \sqrt{\frac{2r_1}{r_1 + r_2}}\right).
    $$

2. **Global optimality among two-impulse transfers (Lawden).** Every transfer between the two orbits that uses exactly two impulses has total $\Delta v \ge \Delta v_H$. More generally, between two coaxial coplanar ellipses the optimal two-impulse transfer applies its impulses at the apses.

With three or more impulses the Hohmann transfer need not be optimal. For large enough $r_2/r_1$, a bi-elliptic transfer through an intermediate apoapsis beyond $r_2$ costs less.

**Proof of part 1.** By the [vis-viva equation](vis-viva.md), a point at radius $r$ on an orbit with semi-major axis $a$ has speed $\sqrt{\mu(2/r - 1/a)}$. The transfer ellipse has $a = (r_1 + r_2)/2$, and the circular speeds are $\sqrt{\mu/r_i}$. Each impulse is tangential, so its magnitude is the difference of the speeds at that radius.

**Part 2** is proved by writing the two-impulse cost as a function of the periapsis radius and the inverse apoapsis radius of the transfer conic, and showing by elementary monotonicity arguments that moving either impulse toward an apse lowers the cost.

## Depends on

- [Vis-viva equation for a state of negative energy](vis-viva.md)
- [Vis-viva after a tangential impulse, for v ≠ 0 and negative new energy](vis-viva-tangential-impulse.md)

## Background

- [Mission resource ledgers and burn costs](../../flight-and-spaceflight/mission-resource-ledgers-and-burn-costs/README.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Keplerian conic orbits: a bound two-body orbit is an ellipse determined by its periapsis and apoapsis radii, with energy $-\mu/(r_p + r_a)$ and the corresponding apsidal speeds (statement prerequisite; not yet stated).
- Proof of part 2 from the conic parametrization of two-impulse transfers (proof prerequisite; not yet stated).

## Sources

- M. Pontani, "Simple method to determine globally optimal orbital transfers", *Journal of Guidance, Control, and Dynamics* 32(3), 2009, <http://reprints.gravitywaves.com/Aerospace/Trajectory/Pontani-2002_SimpleMethodToDeterminGloballyOptimalOrbitalTransfers_JGCD.pdf>:
    - Introduction: Hohmann's conjecture, Lawden's proofs of the global optimality of the Hohmann transfer among two-impulse transfers, and Edelbaum's bi-elliptic transfer;
    - Section III: two-impulse transfers between elliptic orbits compared by elementary calculus, so that the optimal path places its impulses at the apses and the Hohmann transfer is globally optimal among two-impulse transfers;
    - Section III.C: multiple-impulse transfers.
