# Malécot's identity-by-descent model

Let $\mu$ be a measure on a measurable space $\Omega$ and $\iota$ a set of individuals; individual $i$ carries the gene copies $(i, 0)$ (paternal) and $(i, 1)$ (maternal). An identity-by-descent model at a biallelic locus consists of

- a real number $p$ with $0 < p < 1$ (the reference-allele frequency of a polymorphic locus);
- for each gene copy $c$, a measurable function $a_c : \Omega \to \{0, 1\}$ (the reference-allele indicator);
- real numbers $\mathrm{ibd}(c, d)$ for pairs of gene copies,

such that $\int a_c \, d\mu = p$ and $\int a_c a_d \, d\mu = p^2 + p(1 - p)\, \mathrm{ibd}(c, d)$ for all copies $c, d$.

In Malécot's model $\mathrm{ibd}(c, d) \in [0, 1]$ is the probability that the two copies are identical by descent (identical copies carry the same allele, others independent alleles of frequency $p$; Malécot 1948); here $\mathrm{ibd}$ may be any real number, for example a correlation relative to a reference population.

## Sources

- G. Malécot, *Les mathématiques de l'hérédité*, Masson, Paris (1948).
