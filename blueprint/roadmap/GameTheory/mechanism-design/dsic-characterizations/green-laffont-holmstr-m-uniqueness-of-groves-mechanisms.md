# Green–Laffont–Holmström uniqueness of Groves mechanisms

Let $M$ be a direct quasilinear mechanism whose outcome rule maximizes reported welfare. If $M$ is DSIC on the unrestricted domain $\mathbb{R}^\Omega$ (Green–Laffont), or more generally on any smoothly connected domain, in particular any convex domain with no finiteness assumption on $\Omega$ (Holmström), then $M$ is a Groves mechanism: each payment has the form $h_i(b_{-i}) - \sum_{j \ne i} b_j(f(b))$. Connectedness is necessary: on a disconnected domain there are DSIC welfare-maximizing mechanisms that are not Groves.

## Proof sketch

Fix $b_{-i}$. Incentive compatibility bounds the change of agent $i$'s payment between nearby valuations by the change in the others' welfare at the chosen outcomes, from both sides; along a smooth path these bounds integrate to show that payment plus others' welfare is constant along the path.

## Depends on

- [Groves payment](../vickrey-clarke-groves-mechanisms/groves-payment.md)
- [Social welfare](../vickrey-clarke-groves-mechanisms/welfare.md)
- [Dominant-strategy incentive compatibility](../revelation-principle/is-dominant-strategy-incentive-compatibl.md)

## Proof depends on

- [Vickrey–Clarke–Groves theorem](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-groves.md)
- [Taxation principle](taxation-principle.md)

## Sources

- Jerry Green and Jean-Jacques Laffont, "Characterization of Satisfactory Mechanisms for the Revelation of Preferences for Public Goods", Econometrica, 1977.
- Bengt Holmstrom, "Groves' Scheme on Restricted Domains", Econometrica, 1979.
- Noam Nisan, "Introduction to Mechanism Design (for Computer Scientists)", Algorithmic Game Theory, Cambridge University Press, 2007.
