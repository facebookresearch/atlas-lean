# Kingman's theorem for the lineage count

For every natural number $n$ and every real $t \ge 0$,

$$P_{n,M}^{\lfloor tM \rfloor} \to e^{t G_n}$$

entrywise as the natural number $M$ tends to infinity, where $P_{n,M}$ is the [Wright–Fisher transition matrix of the lineage count](wf-lineage-matrix.md) and $G_n$ the [generator of Kingman's block-counting process](block-counting-generator.md). So after $\lfloor tM \rfloor$ generations the transition matrix of the Wright–Fisher ancestral lineage count converges to the transition matrix at time $t$ of the pure-death process with rates $\binom{k}{2}$.

## Sources

- J. F. C. Kingman, *The coalescent*, Stochastic Process. Appl. 13 (1982), 235–248.
- J. F. C. Kingman, *On the genealogy of large populations*, J. Appl. Probab. 19A (1982), 27–43.
- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer (2008), ch. 1.
