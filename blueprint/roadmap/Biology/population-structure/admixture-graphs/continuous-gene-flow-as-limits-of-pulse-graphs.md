# Donor-edge ancestry under repeated pulses and its constant-rate limit

Fix $t\in\mathbb N$ and $m\in[0,1]$. Construct a finite admixture graph
with distinct nodes $R,A_0,\ldots,A_t,B_0,\ldots,B_t$.
The root $R$ has no parent. Both $A_0$ and $B_0$ have the sole parent
$R$, with weight one. For $k\ge1$, $B_k$ has parent $B_{k-1}$ with
weight one, while $A_k$ has parents $A_{k-1}$ and $B_k$ with weights
$1-m$ and $m$. All other proportions are zero.

Let $e=(B_0,R)$ be the distinguished **donor edge**, and let $w_t$ be
its canonical lineage weight for $A_t$. Then

$$w_t=\operatorname{visit}(A_t,B_0)=1-(1-m)^t.$$

The donor edge is not the shared root: every ancestry visits $R$, but
recipient ancestry avoiding all pulses never visits $B_0$.
For fixed $\mu,s\ge0$, set $m_K=\mu/K$ and $t_K=\lfloor Ks\rfloor$.
Along positive integers $K>\mu$, these are admissible graphs, and

$$w_{t_K}(m_K)\longrightarrow1-e^{-\mu s}.$$

Thus a single pulse with that limiting proportion matches this one
scalar donor-edge weight. This is not convergence of the whole graph,
of genealogies, or of all f-statistics.

## Depends on

- [Admixture graph](admixture-graph.md)
- [Lineage weight of an edge](weight.md)

## Proof depends on

- [First-step equation for visit probabilities](visit-eq.md)

## Expansion

The graph is an admixture graph in the canonical sense, including at $m=0,1$:
non-root parent sets have one or two distinct nodes, proportions are
nonnegative and sum to one. Give $R$ rank zero, $B_k$ rank $2k+1$ and
$A_k$ rank $2k+2$. Every parent has smaller rank, proving well-foundedness.
Zero-weight listed parents are permitted by that definition.

First-step recursion gives $\operatorname{visit}(B_k,B_0)=1$ and
$\operatorname{visit}(A_0,B_0)=0$. Applying it to the **same target**
$B_0$ at every recipient node gives
$w_k=m+(1-m)w_{k-1}$. Induction yields the displayed formula, including
$t=0$ with the empty product equal to one. Since the only edge out of
$B_0$ has weight one, its edge weight equals its visit probability.
This identifies a genuine canonical edge weight, not a sum of visits
to differently aged donor nodes.

If $\mu=0$ or $s=0$, the limit is immediate. Otherwise, for sufficiently
large $K$, let $x=\mu/K\in(0,1)$. Integrating $1/(1-u)$ between $0$ and
$x$ gives $-x/(1-x)\le\log(1-x)\le-x$. Since
$t_K/K\to s$, multiplication by $t_K$ and squeezing show
$t_K\log(1-\mu/K)\to-\mu s$. Continuity of the exponential proves the
limit. Restricting to $K>\mu$ avoids negative mixture weights and the
logarithm at zero; it discards only a finite initial segment.

Convergence of f-statistics remains a separate quantitative target.
It needs specified edge-length scaling on both lineages and control
of the resulting edgewise covariance sums. Pulses enter at different
depths, so total donor weight alone cannot identify those sums or
justify replacing the graph by a single pulse. Characterizing all
attainable f-statistic vectors is outside this contract; no claim that
this is an open problem throughout the literature is made.

## Sources

- B. M. Peter, "Admixture, Population Structure, and F-Statistics", *Genetics* 202(4) (2016), 1485–1501, <https://doi.org/10.1534/genetics.115.183913>, population-structure models and Discussion, <https://pmc.ncbi.nlm.nih.gov/articles/PMC4905545/>. This is context for structure versus admixture; the explicit graph, recurrence and scaling limit above are derived here, not claimed as a theorem quoted from that paper.
