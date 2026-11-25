# Lineages of the spatial Λ-Fleming–Viot model with bounded event radius

Let reproduction events $(t, x, r, u)$ form a Poisson point process on $\mathbb R \times \mathbb R^d \times (0, R_0] \times (0, 1]$ with intensity $dt\, dx\, \zeta(dr, du)$, $\zeta$ a finite measure. Following an
event, each ancestral lineage in the closed ball $B(x, r)$ is affected independently with probability $u$, a parent location $z$ is drawn uniformly from $B(x, r)$,
and all affected lineages jump to $z$; if two or more are affected, their blocks merge into one. The state of $n$ lineages is a labelled partition: a
partition $\pi$ of $\{1, \dots, n\}$ with a location in $\mathbb R^d$ for each block. Distinct blocks may share a location. With $V_d$ the volume of the unit ball and
$\Lambda_0 = \int V_d r^d\, \zeta(dr, du)$, the events whose ball contains a given point occur at rate $\Lambda_0 < \infty$. So with $k$ blocks the events that can affect some block
occur at rate at most $k\Lambda_0$, and the process is a well-defined jump-hold process; if $\Lambda_0 = 0$ it is constant. It is the process of [a kernel on a
Poisson clock](../../../Probability/markov-chains/construction-of-markov-chains/uniformized-pure-jump-markov-process-on-a-polish.md) at rate $n\Lambda_0$, with the following kernel: pick a label $i \in \{1, \dots, n\}$ uniformly; if $i$ is not the least label of its block, stay put;
otherwise draw $(r, u)$ with law proportional to $V_d r^d\, \zeta(dr, du)$ and a center $x$ uniform in the ball of radius $r$ around the location of $i$'s block, affect each block
in $B(x, r)$ independently with probability $u$, and keep the event only when $i$'s block is affected and is the lowest-labelled affected block. Each current block is
thus selected at rate $\Lambda_0$ whatever the number $k \le n$ of blocks, and an event affecting exactly a set $A$ of blocks is generated only through the lowest label of $A$, at its
rate under the Poisson description.
For a single lineage the jump rate is $\int u\, V_d r^d\, \zeta(dr, du)$. Two lineages at separation $s$ coalesce at rate $\int u^2\, \mathrm{Vol}\bigl(B(0, r) \cap B(s e_1, r)\bigr)\, \zeta(dr, du)$. From
separation $0$, an event covering both makes exactly one of them jump with probability $2u(1 - u)$ and merges them with probability $u^2$, so an uncoalesced
pair at distance $0$ is not the coalesced state. The displacement of two uncoalesced lineages is a Markov process on $\mathbb R^d$ together with a coalesced
state. Because events are balls, its norm is a Markov process on $[0, \infty)$ together with that state. After coalescence, the surviving block moves at the
single-lineage rate. The radial reduction uses the ball shape: for axis-aligned square events $[x - r, x + r]^2$ in $d = 2$, the coalescence rate at
displacement $v$ is $\int u^2 (2r - |v_1|)^+ (2r - |v_2|)^+\, \zeta(dr, du)$, which for $r = 1$, $u = 1$ and $|v| = 1$ is $2$ along an axis and $(2 - 1/\sqrt2)^2 \approx 1.67$ along a diagonal, so the
norm of the displacement is not Markov there.

## Depends on

- [A Markov kernel run on a Poisson clock is a pure-jump Markov process](../../../Probability/markov-chains/construction-of-markov-chains/uniformized-pure-jump-markov-process-on-a-polish.md)

## Sources

- N. H. Barton, A. M. Etheridge and A. Véber, "A new model for evolution in a spatial continuum", arXiv:0904.0210 (2010), Section 2: Definition 2.2, Notation 2.5, the lineage dynamics and the rates (6)–(7) (stated there for $d = 2$).
