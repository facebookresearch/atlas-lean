# Square law for mine ventilation networks

In a ventilation network with node continuity and signed branch flows, let each branch obey the stipulated square law
$\Delta p = R\,Q\lvert Q\rvert$ with an actual-state coefficient $R \ge 0$. If starting from a reference-density Atkinson
resistance, include the actual-to-reference density ratio in this coefficient. Then $Q\,\Delta p \ge 0$ on every branch. Branches in series carrying the same
flow have $R_{\mathrm{eq}} = \sum_i R_i$. For a nonempty family of branches in parallel between the same two nodes, with a common
pressure drop and flow direction and every $R_i > 0$, the equivalent resistance satisfies
$1/\sqrt{R_{\mathrm{eq}}} = \sum_i 1/\sqrt{R_i}$. A branch with $R=0$ forces the common pressure drop to zero, so every positive-resistance branch carries zero flow; the
reciprocal formula does not apply. For a prescribed total flow, the zero-resistance branches carry all of it. With exactly one
such branch the split is unique. With at least two and a nonzero total flow, the same-direction split among them is not unique. Solving networks and regulatory compliance are outside this result.

## Depends on

## Proof depends on

## Sources

- *Atkinson resistance*, Wikipedia: the density-corrected square law $\Delta P = (\rho_{\mathrm{actual}}/\rho_{\mathrm{ref}})R_{\mathrm{ref}}Q^2$ for mine airways, <https://en.wikipedia.org/wiki/Atkinson_resistance>.
