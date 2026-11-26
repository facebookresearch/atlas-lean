# Regeneration process for evolutionary innovation

A new function requires a target sequence that is $k$ mutational steps away from a starting sequence; the intermediate steps are neutral and only the final product is favoured by selection. In the **regeneration process**, the starting sequence is produced from the wild type at rate $w$ (by gene duplication or recombination), each step towards the target occurs at rate $u$, and each intermediate is destroyed by an inactivating mutation at rate $v$, returning it to the wild-type pool. Let $x_0$ be the frequency of the wild type and $x_i$ ($i \ge 1$) the frequency of sequences that have made $i$ steps towards the target. Ignoring the (rare) target class, the neutral steady state is

$$x_0 = \frac{v}{v + w}, \qquad x_i = \frac{w}{u}\,\frac{v}{v + w} \left(\frac{u}{v + u}\right)^{i}, \quad i \ge 1.$$

In particular $x_i$ decays geometrically in $i$ with ratio $u/(u+v)$, so the expected time for the population to produce the target grows exponentially in the number of required steps $k$, but not in the gene length $L$: the starting condition is regenerated continually and failed searches are discarded, so only polynomially many searches in $L$ are needed, whereas a single unregenerated random-walk search in the $4^L$-sequence space takes time exponential in $L$.

Example: with $w = 10^{-7}$, $u = 10^{-9}$ and $v = 10^{-7}$ per cell division, $x_{10} \approx 5 \times 10^{-19}$, so cells ten steps from the target are present in a planetary bacterial population of order $10^{30}$ cells.

## Expansion

Balance of flows at steady state: class $1$ receives $w x_0$ and loses $(u + v)x_1$, so $x_1 = w x_0/(u+v)$; class $i \ge 2$ receives $u x_{i-1}$ and loses $(u+v)x_i$, so $x_i = x_{i-1}\,u/(u+v)$. Together $x_i = \frac{w x_0}{u}\left(\frac{u}{u+v}\right)^i$. The intermediate classes then sum to $\frac{w x_0}{u+v}\cdot\frac{1}{1 - u/(u+v)} = \frac{w x_0}{v}$, and normalization $x_0(1 + w/v) = 1$ gives $x_0 = v/(v+w)$. For the example, $x_{10} = 100 \cdot \tfrac12 \cdot (1/101)^{10} \approx 4.5 \times 10^{-19}$. Sexual reproduction and exchange of genetic material can further increase search efficiency by a linear factor.

## Sources

- A. H. Knoll and M. A. Nowak, "The timetable of evolution", Science Advances 3(5) (2017), e1603076, section on evolutionary innovation and Figure 3 ("The regeneration process"), <https://doi.org/10.1126/sciadv.1603076>, PMCID: PMC5435417.
