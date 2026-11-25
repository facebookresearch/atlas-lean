# Local trees are not Markov along the sequence

Take $n = 2$ samples, recombination intensity $\rho > 0$, and three loci $x_1 < x_2 < x_3$, with coalescence times $T_{x_1}, T_{x_2}, T_{x_3}$. Then $(T_{x_1}, T_{x_2}, T_{x_3})$ is not a Markov chain in the order of the loci. The witness does not depend on the choice of versions of the conditional laws:

1. By [the joint law of the two-locus coalescence times](two-locus-n-2-joint-law-of-t-a-t-b-is-diagonal-a.md), which is an atom on the diagonal plus an absolutely continuous part, the conditional law of $T_{x_3}$ given $T_{x_2}$ has no atom except at $T_{x_2}$.
2. Hence if the triple were Markov, then for every version $K$ of that conditional law

$$\mathbb{P}\bigl(T_{x_3} = T_{x_1} \ne T_{x_2}\bigr) = \mathbb{E}\bigl[\mathbf{1}\{T_{x_1} \ne T_{x_2}\}\, K(T_{x_2}, \{T_{x_1}\})\bigr] = 0.$$

3. In the ancestral recombination graph this probability is positive. The lineage of sample $1$ recombines at a breakpoint $b_1 \in (x_1, x_2]$, its right part recombines at $b_2 \in (x_2, x_3]$, and the parts carrying $x_1$ and $x_3$ coalesce. Then the part carrying $x_2$ meets the lineage of sample $2$ first, and the lineage carrying $\{x_1, x_3\}$ meets it later.

## Depends on

- [Two-locus n = 2: joint law of the coalescence times is a diagonal atom plus an absolutely continuous part](two-locus-n-2-joint-law-of-t-a-t-b-is-diagonal-a.md)

## Proof depends on

- [Continuum ARG with homogeneous recombination: finite-locus marginals and two-point law](continuum-arg-homogeneous-rho-dx-finite-locus-ma.md)

## Expansion

1. An explicit positive lower bound on $\mathbb{P}(T_{x_3} = T_{x_1} \ne T_{x_2})$ from the composite event of step 3.
2. The argument of step 2, using an event probability rather than pointwise conditional laws.

## Sources

- C. Wiuf and J. Hein, Recombination as a point process along sequences, *Theor. Popul. Biol.* 55 (1999), 248–259, <https://pubmed.ncbi.nlm.nih.gov/10366550/> (the remark that local trees are not Markov).
- G. A. T. McVean and N. J. Cardin, Approximating the coalescent with recombination, *Philos. Trans. R. Soc. B* 360 (2005), 1387–1393, <https://pubmed.ncbi.nlm.nih.gov/16048782/> (motivation for the sequentially Markov coalescent).
