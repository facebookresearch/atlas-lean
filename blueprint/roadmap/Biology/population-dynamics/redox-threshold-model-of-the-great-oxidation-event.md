# Redox threshold model of the Great Oxidation Event

Two primary producers compete for a limiting nutrient: anoxygenic photosynthetic bacteria with density $x_1$, which need ferrous iron, and cyanobacteria with density $x_2$, which split water and release oxygen. With total density $x = x_1 + x_2$, reproductive rates $r_1, r_2 > 0$, competition coefficient $c > 0$ and small immigration rates $u_1, u_2 > 0$ from refuge niches,

$$\dot x_1 = x_1(r_1 z_1 - c x) + u_1, \qquad \dot x_2 = x_2(r_2 - c x) + u_2,$$

where $z_1$ is the availability of ferrous iron. Oxygen $z_2$ is produced by cyanobacteria and removed at rate $b$ by respiration and geophysical sinks,

$$\dot z_2 = a x_2 - b z_2, \qquad \text{with steady state } z_2 = \frac{a x_2}{b},$$

and oxygen depletes iron, $z_1 = 1/(1 + \alpha z_2)$ at steady state.

Before oxygenation $z_1 \approx 1$ and anoxygenic phototrophs dominate if $r_1 > r_2$. If the oxygen removal rate $b$ declines slowly (over millions of years), oxygen rises slowly and $z_1$ falls until the effective growth rate of anoxygenic phototrophs drops below that of cyanobacteria,

$$r_1 z_1 < r_2,$$

at which point cyanobacteria rapidly take over, oxygen increases sharply and iron availability collapses, locking in the oxic state. A gradual change in a physical parameter thus produces an abrupt ecological transition.

## Expansion

The oxygen equation alone gives $z_2 = a x_2/b$: steady-state oxygen is proportional to cyanobacterial biomass, so an increase in oxygen can come either from more cyanobacteria (with $z_2/x_2 = a/b$ fixed) or from a smaller removal rate $b$ (raising $z_2/x_2$). In the competition equations, with negligible immigration, the producer with the larger per-capita growth rate excludes the other, since both share the density-dependent death rate $c x$; the dominant type switches when $r_1 z_1$ crosses $r_2$. Because cyanobacterial takeover raises $z_2$, which further lowers $z_1$, the switch is self-reinforcing, giving the sharp transition. The model is deliberately oversimplified to illustrate how geochemical change in sinks, rather than the origin of oxygenic photosynthesis, could time the transition.

## Sources

- A. H. Knoll and M. A. Nowak, "The timetable of evolution", Science Advances 3(5) (2017), e1603076, section "The GOE and its biological consequences" and Box 1 ("A simple model for the GOE"), <https://doi.org/10.1126/sciadv.1603076>, PMCID: PMC5435417.
