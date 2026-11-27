# Termination of the reduced finite-locus ancestral recombination graph

Let $n \ge 1$ sequences be sampled at finitely many loci on a chromosome, with total scaled recombination rate $\rho \ge 0$ across the chromosome, and run the [marked whole-chromosome finite-locus ancestral recombination graph](marked-whole-chromosome-unreduced-finite-locus-a.md) together with its reduction map. Let $T_{\mathrm{GMRCA}}$ be the first time the whole-chromosome graph has a single lineage, and $\tau_{\mathrm{red}}$ the first time the reduced graph has every locus at its most recent common ancestor. Then $\tau_{\mathrm{red}} \le T_{\mathrm{GMRCA}}$ almost surely, and $\mathbb E\,T_{\mathrm{GMRCA}} < \infty$, so $\tau_{\mathrm{red}}$ is almost surely finite with finite mean.

The number of lineages of the whole-chromosome graph is the [ancestral line count with recombination](lineage-count-birth-death-chain-rho-0-positive-r.md): it jumps from $k$ to $k+1$ at rate $\rho k/2$ and to $k-1$ at rate $\binom k2$. For $\rho > 0$ this chain is positive recurrent, so its hitting time of $1$ from $n$ has finite mean; for $\rho = 0$ it is a pure death process absorbed at $1$, with mean absorption time $2(1 - 1/n)$, and then $\tau_{\mathrm{red}} = T_{\mathrm{GMRCA}}$ is the time to the most recent common ancestor of Kingman's coalescent. No recurrence is claimed for the number of lineages of the reduced graph.

## Depends on

- [Marked whole-chromosome (unreduced) finite-locus ARG and the reduction map](marked-whole-chromosome-unreduced-finite-locus-a.md)
- [The ancestral line count with recombination is positive recurrent](lineage-count-birth-death-chain-rho-0-positive-r.md)

## Expansion

A full proof page must still establish:

- that the reduction map sends the whole-chromosome graph at time $T_{\mathrm{GMRCA}}$ to a reduced graph with every locus resolved, which gives $\tau_{\mathrm{red}} \le T_{\mathrm{GMRCA}}$ pathwise;
- the bound $\mathbb E\,\tau_{\mathrm{red}} \le \mathbb E_n T_1$ from the line-count chain, for $\rho > 0$ and for $\rho = 0$;
- for $\rho = 0$, the identity $\tau_{\mathrm{red}} = T_{\mathrm{GMRCA}}$.

## Sources

- R. C. Griffiths and P. Marjoram, "An ancestral recombination graph", 1997, <https://research.monash.edu/en/publications/an-ancestral-recombination-graph/>
- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer, 2008, Chapter 3, <https://rd.springer.com/book/10.1007/978-0-387-78168-6>
