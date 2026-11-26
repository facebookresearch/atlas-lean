# Within-host reproduction number with eclipse phase and virion absorption

Let $T$ be uninfected target cells, $I_1$ infected cells in the eclipse phase, $I_2$ productively
infected cells and $V$ free virus, all nonnegative, with infection rate constant $\beta > 0$,
eclipse exit rate $k > 0$, infected-cell death rate $\delta > 0$, virion production rate per
productive cell $p > 0$ and virion clearance rate $c > 0$. Over the time scale of an acute
infection, target-cell proliferation and natural death are neglected:

$$
\frac{dT}{dt} = -\beta V T, \qquad
\frac{dI_1}{dt} = \beta V T - k I_1, \qquad
\frac{dI_2}{dt} = k I_1 - \delta I_2, \qquad
\frac{dV}{dt} = p I_2 - c V - \beta V T .
$$

At the infection-free state $(T_0, 0, 0, 0)$ the within-host basic reproduction number, the mean
number of cells infected by one infected cell early in infection, is

$$R_0 = \frac{p\,\beta\, T_0}{\delta\,(c + \beta T_0)} .$$

The linearization at $(T_0,0,0,0)$ has a positive eigenvalue (initial exponential growth of virus)
if and only if $R_0 > 1$. An antiviral that blocks virion production with effectiveness
$\varepsilon \in [0,1]$ ($p \mapsto (1-\varepsilon)p$) gives $(1-\varepsilon)R_0$.

## Depends on

- [Next-generation matrix and the basic reproduction number](../../next-generation-matrix-and-the-basic-reproductio/README.md)

## Expansion

Every eclipse-phase cell survives to become productive (there is no death in $I_1$), and a
productive cell lives for mean time $1/\delta$, releasing $p/\delta$ virions. A free virion near
the infection-free state is removed at total rate $c + \beta T_0$ and infects a cell with
probability $\beta T_0/(c + \beta T_0)$; the product is $R_0$. The term $-\beta V T$ in the virus
equation accounts for virions consumed by entry, which is why $\beta T_0$ appears in the
denominator; without it $R_0$ would be $p\beta T_0/(\delta c)$. In the linearized
$(I_1, I_2, V)$ system the transmission matrix has rank one, so the next-generation matrix is a
scalar equal to $R_0$ and the threshold for growth follows from the next-generation theorem.
Because the target-cell pool is not replenished, every infection eventually resolves; $R_0$
controls only the initial growth and, through target-cell depletion, the peak. The source assumes
that any antiviral reduces $R_0$ by the factor $1 - \varepsilon$, which is exact for production
blocking; blocking entry ($\beta \mapsto (1-\varepsilon)\beta$) also changes the absorption term.

## Sources

- A. Gonçalves, J. Bertrand, R. Ke, E. Comets, X. de Lamballerie, D. Malvy, A. Pizzorno,
  O. Terrier, M. Rosa Calatrava, F. Mentré, et al., "Timing of antiviral treatment initiation is
  critical to reduce SARS-CoV-2 viral load", CPT: Pharmacometrics & Systems Pharmacology 9 (2020),
  Methods, "Model" (Eqs. 1-2) and "Predicting the effects of
  treatment", <https://doi.org/10.1002/psp4.12543> (PMC7323384).
