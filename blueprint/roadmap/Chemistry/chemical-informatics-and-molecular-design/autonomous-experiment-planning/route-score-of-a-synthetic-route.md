# Route score of a synthetic route

A synthetic route is scored by what it costs to run: human and machine time weighted by their hourly rates, multiplied by the money spent on labour and materials and by the mass of material consumed, summed over steps and divided by the amount of target produced.

For one step, let $t_{\mathrm{H}}, t_{\mathrm{M}} \ge 0$ be the human and machine times, $C_{\mathrm{H}}, C_{\mathrm{M}} > 0$ the corresponding hourly costs, and let reactant or reagent $i$ enter in molar amount $n_i \ge 0$ at cost $C_i$ per unit amount and molar mass $\mathrm{MW}_i$. The total time cost and the step score are

$$
\mathrm{TTC} = \sqrt{\Big(\frac{C_{\mathrm{H}}}{C_{\mathrm{M}}} t_{\mathrm{H}}\Big)^{2} + \Big(\frac{C_{\mathrm{M}}}{C_{\mathrm{H}}} t_{\mathrm{M}}\Big)^{2}} ,
$$

$$
\mathrm{StepScore} = \mathrm{TTC} \times \Big( \sum_{\mathrm{H},\mathrm{M}} t_{\mathrm{H},\mathrm{M}} C_{\mathrm{H},\mathrm{M}} + \sum_i n_i C_i \Big) \times \sum_i n_i \mathrm{MW}_i ,
$$

and for a route of steps $N$ producing an amount $n_{\mathrm{Target}} > 0$ of the target,

$$
\mathrm{RouteScore} = \frac{\sum_{N} \mathrm{StepScore}_{N}}{n_{\mathrm{Target}}} .
$$

Smaller is better. The quantity carries units: time $\times$ money $\times$ mass per amount of substance, for instance hours $\times$ currency $\times$ gram per mole in the source's reporting.

Conventions and limits. The cost ratios need both hourly costs positive, and the normalization needs a route that produces a positive amount, so a failed route is left unscored. The source reports a purely manual step as $\mathrm{TTC} = t_{\mathrm{H}}$, which is a separate reporting convention and not the general formula at $t_{\mathrm{M}} = 0$. Yields enter the score through the amounts, and where no better estimate exists the source assumes unit yield.

## Depends on

- [Molar mass of a sample](../../amounts-and-stoichiometry/amount-of-substance-and-molar-mass/molar-mass.md)

## Proof depends on

None.

## Expansion

A formal development takes positive hourly costs, nonnegative times and amounts, a positive target amount, and defines the three quantities by the displays. Worth recording are the degenerate cases: zero machine time gives $\mathrm{TTC} = (C_{\mathrm{H}}/C_{\mathrm{M}})t_{\mathrm{H}}$ from the formula, and equal hourly costs give the Euclidean norm of the time pair.

## Context

Graduate; a cost model, not a law. Seifrid, Hickman, Aguilar-Granda, Lavigne, Vestfrid, Wu, Gaudin, Hopkins and Aspuru-Guzik propose it so that routes proposed by a self-driving laboratory are compared by the resources they consume rather than by step count.

## Sources

- Martin Seifrid, Riley J. Hickman, Andrés Aguilar-Granda, Cyrille Lavigne, Jenya Vestfrid, Tony C. Wu, Théophile Gaudin, Emily J. Hopkins and Alán Aspuru-Guzik, *Routescore: Punching the Ticket to More Efficient Materials Development*, ACS Central Science 8 (2022) 122–131, Eqs. 1–3 and the surrounding text, including the manual-step convention and the unit-yield assumption. DOI [10.1021/acscentsci.1c01002](https://doi.org/10.1021/acscentsci.1c01002), PMC8796309.
