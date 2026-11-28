# Langmuir isotherm

The Langmuir isotherm is the coverage model $\theta = bP/(1+bP)$ for adsorption on identical, independent, singly occupied sites.

Let an adsorbent carry adsorption sites of which a fraction $\theta \in [0,1]$ is occupied at equilibrium with a gas of
pressure $P \ge 0$ at fixed temperature $T$. The Langmuir isotherm with affinity constant $b > 0$ (units of inverse
pressure, a function of $T$) is

$$
\theta(P) = \frac{bP}{1+bP}, \qquad q(P) = q_{\max}\,\theta(P),
$$

where $q_{\max} > 0$ is the amount adsorbed at full occupancy (the monolayer or site capacity). The model is
motivated by two hypotheses of the cited treatment: adsorption occurs only at specific localized sites, with saturation
at complete occupancy, and $b$ is constant with respect to coverage, as when the enthalpy of adsorption does not depend
on coverage; these are model assumptions, not consequences of the formula. On $P \ge 0$ the function $\theta$ is
strictly increasing with $\theta(0) = 0$, satisfies $\theta(P) < 1$ for every finite $P$, and $\theta(P) \to 1$ as
$P \to \infty$; its initial slope is $b$, so $q \approx q_{\max} b P$ at low pressure.

## Context

Undergraduate level. The Langmuir model is the reference single-site isotherm against which the gas uptake of microporous solids, including metal–organic frameworks, is fitted and compared. The same algebraic law written with a liquid-phase concentration, as on the batch-adsorber page of this field, is a separate stipulated model.

## Depends on

None.

## Proof depends on

None.

## Expansion

The monotonicity and limits follow from $\theta(P) = 1 - 1/(1+bP)$. Real adsorbents with heterogeneous sites deviate
from the model, which motivates the dual-site and Langmuir–Freundlich models.

## Sources

- R. Nix, *Surface Science*, LibreTexts Chemistry (Queen Mary, University of London), Section 3.3, "Langmuir Isotherm from a Kinetics Consideration", Assumptions 1 and 2 and the displayed equations $P(1-\theta)/\theta = B(T)$ and $\theta = bP/(1+bP)$, [chem.libretexts.org](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Surface_Science_%28Nix%29/03:_The_Langmuir_Isotherm/3.03:_Langmuir_Isotherm_from_a_Kinetics_Consideration).
