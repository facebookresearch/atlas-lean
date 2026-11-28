# Evolutionary safety condition for a mutagenic drug

Call a treatment **evolutionarily safe** if it does not increase the number of mutants generated in
a treated host above the number expected without treatment. In the simplified within-host model
that follows only the growth phase of length $T$, with replication rate $b$, $m$ positions that are
lethal when mutated, natural mutation rate $u_0$ per base and treatment mutation rate
$u_1 = s\,u_0$ for a fold increase $s > 1$, the mutant abundance at time $T$ is a one-humped
function of the mutation rate, maximal near $u^\ast = 1/(b T m)$. Write $h = bT$ and $n$ for the
number of positions whose mutation gives the mutant of concern. To first order in the mutation rate,
approximating $(1-u)^{m+n} \approx 1 - u(m+n)$ and $1 - e^{-hnu} \approx hnu$ (valid when $mu$ and
$hnu$ are small), the evolutionary risk factor, the ratio of mutant abundance with and without
treatment, becomes $\mathrm{ERF} \approx u_1 e^{-hmu_1}/(u_0 e^{-hmu_0})$. Within this
approximation, treatment is evolutionarily safe ($\mathrm{ERF} < 1$) exactly when

$$m \ >\ \frac{\log s}{b\,T\,u_0\,(s - 1)} .$$

The condition is therefore an approximate criterion for the simplified model, not an exact
equivalence. If $u_0 > u^\ast$ the virus already sits beyond the hump and any increase in the
mutation rate is safe. In the full model, which adds a clearance phase with clearance rate $a_1$,
evolutionary safety improves as $a_1$ decreases, and the source interprets the inequality as a
sufficient condition (an upper bound on the number of lethal positions needed) there.

## Depends on

- [Wild-type and mutant dynamics under mutagenesis](wild-type-and-mutant-dynamics-under-mutagenesis.md)

## Remarks

Raising the mutation rate has two opposing effects: each replication is more likely to produce the
mutant of concern, but fewer replications occur because more progeny are inviable. The second
effect wins once the genome is long enough, which is what the condition measures: safety requires
many lethal positions, a long growth phase, or a large fold increase $s$, since the right-hand side
decreases in all three. The criterion gives a design target for mutagenic drugs: a larger fold
increase in mutation rate is safer, not more dangerous.

## Sources

- G. Lobinska, Y. Pilpel, M. A. Nowak, "Evolutionary safety of lethal mutagenesis driven by antiviral
  treatment", PLoS Biology 21 (2023) e3002214, Eq. (4) and Methods Eqs. (25)–(33),
  <https://doi.org/10.1371/journal.pbio.3002214> (PMC10409280).
