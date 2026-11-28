# Backward migration rates under time-varying population sizes

Measure time $t \ge 0$ backwards from the present. For populations $A$ and $B$, let $\nu_a(t), \nu_b(t) > 0$ be the effective population size functions (in time units, so that the pairwise coalescence rate in $A$ is $1/\nu_a(t)$), and let $m_{a\to b}(t), m_{b \to a}(t) \ge 0$ be **emigration fractions**: the fraction of population $A$ (resp. $B$) emigrating to the other population per unit time, so that the forward flow of migrants from $A$ to $B$ is $m_{a\to b}(t)\,\nu_a(t)$.

**Coalescence.** Two lineages in $A$ coalesce at time $t$ with density

$$f(t) = \frac{1}{\nu_a(t)} \exp\!\Big(-\int_0^t \frac{dx}{\nu_a(x)}\Big).$$

**Backward migration.** A lineage in $A$ has its parent in $B$ (a backward move $A \to B$) at instantaneous rate equal to the ratio of immigrants into $A$ to the size of $A$,

$$f_{a \to b}(t) = \frac{m_{b \to a}(t)\,\nu_b(t)}{\nu_a(t)},$$

and the waiting time to such an event has density $r_{a\to b}(t) = f_{a\to b}(t)\exp\!\big(-\int_0^t f_{a\to b}(x)\,dx\big)$.

**Competing events.** From the current time $\tau$, with $l_k$ lineages in each current species $k$, coalescences in species $k$, at rate $\binom{l_k}{2}/\nu_k(t)$, and migrations from $k$ to $k'$, at rate $l_k\, f_{k \to k'}(t)$, are independent non-homogeneous Poisson processes. The next event is the one with the smallest waiting time, and the waiting time $w$ of an event with rate $h(t)$ is drawn by solving

$$\int_\tau^{\tau + w} h(s)\,ds = -\log(1 - U), \qquad U \sim \mathrm{Uniform}(0, 1),$$

with an independent $U$ for each event.

On intervals where $\nu_a, \nu_b, m$ are linear, the migration rate $f_{a \to b}$ has the form $\frac{(a_1 + b_1 t)(a_2 + b_2 t)}{a_3 + b_3 t}$. If $b_3 \ne 0$, polynomial division gives $c_0 + c_1 t + \frac{c_2}{a_3 + b_3 t}$ for constants $c_0, c_1, c_2$ (the source's Eq. 5); if $b_3 = 0$ (constant $\nu_a$), it is a polynomial in $t$ of degree at most $2$ (quadratic when $b_1 b_2 \ne 0$). In either case it integrates in closed form. When population $B$ splits into $B_1, B_2$, migration between $A$ and $B_1 \cup B_2$ proceeds as if the $B$'s were one population, with immigrants from $A$ divided in proportion to the sizes of $B_1$ and $B_2$.

## Depends on

- [Poisson point process with finite intensity](../../../../Probability/point-processes/poisson-point-processes/poisson-point-process.md)

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Expansion

The backward rate is the continuous-time version of the per-generation backward migration probability in a Wright–Fisher model with migration: each individual of $A$ picks its parent uniformly from the previous generation's members present in $A$, a fraction of whom are immigrants from $B$. Parametrizing by emigration fractions rather than fixed backward rates keeps the interpretation stable when population sizes change, and unequal migration does not alter the population sizes, which remain prescribed. Lineages are moved back in time until a speciation time is reached, where the species are merged; with all functions constant the scheme reduces to the classical island model. A two-parameter "gradual separation" scenario, migration maximal at divergence and declining linearly to zero, generates realistic decreasing gene flow along a species tree.

## Sources

- J. Heled, D. Bryant, A. J. Drummond, "Simulating gene trees under the multispecies coalescent and time-dependent migration", BMC Evolutionary Biology 13 (2013) 44, Methods, Equations 1–5 and the multispecies extension, <https://doi.org/10.1186/1471-2148-13-44>, PMCID PMC3646706.
