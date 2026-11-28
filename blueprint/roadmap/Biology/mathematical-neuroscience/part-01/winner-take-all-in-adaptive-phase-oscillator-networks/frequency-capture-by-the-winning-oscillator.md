# Frequency capture by the winning oscillator under frequency detuning

Consider the star network of adaptive phase oscillators of the dependency below with the specific coupling functions $g(x) = \sin x$, $h(x) = \big((\mu^2 - x^2)/\mu^2\big)^{\sigma}$ for $|x| < \mu$ and $h(x) = 0$ for $\mu \le |x| \le \pi$ (with $\sigma \gg 1$, $0 < \mu < \pi$), and the odd interaction function $f(x) = \sin\!\big(|x - \pi|^{\nu}/\pi^{\nu - 1}\big)$ for $x \in [0, \pi]$ (extended oddly), $\nu > 1$, which has $f'(0) = \nu$, $f'(\pi) = 0$ and its maximum at $x_{max} = \pi(1 - 2^{-1/\nu}) \to 0$ as $\nu \to \infty$. Let the POs be slightly detuned, $\omega_i = \omega + \Delta_i$ with $|\Delta_i| < |b|$, and let $b < 0$ with the WTA points of the identical case stable.

**Statement.** For $\nu$ large and $\mu < \pi/2$, the system has $n$ fixed points $Q_l$, $l = 1, \dots, n$, obtained by continuation of the hyperbolic WTA points $P_{1,l}$; they keep the stability of $P_{1,l}$. At $Q_l$ the central oscillator adopts the frequency of the winner, $\omega_0 \approx \omega_l$, the winner is nearly in phase with the CO, $\phi_l \approx 0$, $a_l \approx c + \gamma$ (exactly, $a_l = c + \gamma h(\phi_l)$), and every loser $i \ne l$ has amplitude $a_i = c$ and phase difference

$$\bar\phi_i \approx \pi - \arcsin\!\Big(\frac{\omega_i - \omega_l}{b}\Big),$$

so $|\bar\phi_i| > \pi/2$: the losers are strongly incoherent with the CO.

## Depends on

- [Stability of synchronization and winner-take-all equilibria](stability-of-synchronization-and-winner-take-all-equilibria.md)

## Expansion

Hyperbolic equilibria persist under small perturbations with unchanged stability, so the $n$ symmetric WTA points survive small detuning. For large $\nu$ the function $f$ is nearly zero away from a small neighbourhood of $0$ except near its extremum close to $0$, so losers far from phase $0$ exert almost no force on the CO and the CO frequency equation at equilibrium forces $\omega_0 = \omega_l$. Each loser equation then reads $0 = \omega_i - \omega_l - b\sin\phi_i$ up to small terms, whose solution on the branch continuing $\phi_i = \pi$ is the displayed formula. As detuning grows beyond $|b|$, saddle-node bifurcations on invariant circles and tori replace these fixed points by non-stationary WTA regimes in which loser phases drift while the winner remains locked; this is described in the source by Propositions 5 and 6.

## Sources

- O. Burylko, Y. Kazanovich, R. Borisyuk, Winner-take-all in a phase oscillator system with adaptation, Scientific Reports (2018), Eqs. (8) to (10) and Proposition 4. <https://doi.org/10.1038/s41598-017-18666-3> PMCID: PMC5765106
