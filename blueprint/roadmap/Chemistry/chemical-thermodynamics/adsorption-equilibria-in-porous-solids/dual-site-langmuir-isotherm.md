# Dual-site Langmuir isotherm

The dual-site Langmuir isotherm adds two independent Langmuir terms, modelling an adsorbent with two kinds of sites.

For pressure (fugacity) $P \ge 0$ the dual-site Langmuir loading is

$$
L(P) = M_1\frac{K_1P}{1+K_1P} + M_2\frac{K_2P}{1+K_2P},
$$

with site capacities $M_1, M_2 > 0$ and affinity constants $K_1, K_2 > 0$ (inverse pressure). It is strictly
increasing on $P \ge 0$, tends to $M_1 + M_2$ as $P \to \infty$, and has the finite Henry constant
$L'(0) = M_1K_1 + M_2K_2$. For $K_1 = K_2$ it reduces to a single Langmuir isotherm with capacity $M_1+M_2$.

## Context

Graduate level. Dual-site fits are the standard description of CO2 and hydrocarbon isotherms in metal–organic frameworks with strong open-metal sites plus weaker pore-wall sites, and they feed directly into ideal adsorbed solution theory because they obey Henry's law.

## Depends on

- [Langmuir isotherm](langmuir-isotherm.md)

## Proof depends on

None.

## Expansion

Each term is a Langmuir isotherm, so the properties follow termwise. The model is a fitted description; its two sites
need not correspond to crystallographically distinct sites.

## Sources

- C. M. Simon, B. Smit and M. Haranczyk, *pyIAST documentation*, sections "Competitive Langmuir adsorption" and "ModelIsotherm" (model list and `spreading_pressure`), [pyiast.readthedocs.io](https://pyiast.readthedocs.io/en/latest/)
