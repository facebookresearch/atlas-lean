# Pairwise mutation counts from an integrable coalescence time

Let $T\ge0$ be a measurable pair coalescence time on a probability
space, with $\mathbb E T<\infty$, and fix $\theta\ge0$.
Assume infinite-sites mutation marking: conditional on the genealogy,
the two separating branches of length $T$ receive independent Poisson
counts of mean $\theta T/2$, and each mutation creates a distinct site.
Their sum $D$ is the number of sequence differences.
Equivalently the pair-count conditional law given $T$ is the kernel
$t\mapsto\operatorname{Poisson}(\theta t)$, with the joint law specified
by the corresponding composition product. Then $D$ is integrable and

$$\mathbb E[D\mid T]=\theta T\quad\text{almost surely},
\qquad\mathbb E D=\theta\mathbb E T.$$

The coalescence time need not be exponential or come from a Kingman
process. The genealogy and the mutation count are not unconditionally
independent. If $\theta=0$ or $T=0$ almost surely, $D=0$ almost surely.
For a unit-rate panmictic pair, $\mathbb E T=1$ gives $\mathbb E D=\theta$.
For $d\ge2$ unit-size symmetric island demes **with positive migration**,
the within-deme mean is $d$ and the corresponding mean difference is
$\theta d$. With zero migration it is instead $\theta$ within a deme.

## Proof depends on

- [Integrability of a conditionally Poisson count](../poisson-mutation-on-the-kingman-genealogy/integrable-nat-cast-of-has-cond-distrib.md)
- [Conditional Poisson mean](../poisson-mutation-on-the-kingman-genealogy/cond-exp-nat-cast-of-has-cond-distrib-po.md)

## Background

- [Existing Kingman genealogy instance](../pairwise-differences-under-poisson-mutation/integral-pair-diff-of-mutation.md)
- [Symmetric-island within-deme mean](within-time.md)

## Expansion

Apply the generic canonical conditional-Poisson results with conditioning
variable $T$ and measurable rate $\rho(t)=\theta t$.
Integrability of $\rho(T)$ follows from that of $T$; integrating the
conditional mean proves the identity.
Those results already live in
`Domains/Biology/PopulationGenetics/Coalescent/Mutation.lean` as
`Coalescent.integrable_natCast_of_hasCondDistrib_poisson` and
`Coalescent.condExp_natCast_of_hasCondDistrib_poisson` within
`MathlibExt.Biology.PopulationGenetics`.
Despite their roadmap folder name they do not require Kingman holding
times. This page is their genealogy application, not a new implementation
of the conditional-Poisson theorem or a second Kingman result.

A general marked-population construction instantiating
`CoalescentFStatistics.CoalescentModel` remains separate.
The count identity alone supplies neither the population allele-frequency
fields nor their square integrability, the sampling convention, the
measure over sites, or the equality of that model's `meanHet` with this
expected sequence-difference count. These bridges must be constructed
before claiming its f-statistic assumption has been discharged.

## Sources

- M. Slatkin, "Inbreeding coefficients and coalescence times", Genetical Research 58 (1991), 167–175, <https://doi.org/10.1017/S0016672300029827> (not opened). The identity is derived above.
