# Viability selection in an inbred population

Let a biallelic locus have genotype frequencies $p^2 + Fpq$, $2pq(1 - F)$ and $q^2 + Fpq$ for $AA$, $Aa$
and $aa$ (the frequencies of an individual with inbreeding coefficient $F \in [0, 1]$, see
[genotype frequencies under inbreeding](genotype-frequencies-under-inbreeding.md)), where $p \in [0, 1]$ is
the frequency of $A$ and $q = 1 - p$. Let the genotypes have nonnegative viabilities $1 + s \ge 0$,
$1 + hs \ge 0$ and $1$, with mean viability

$$\bar w = 1 + s(p^2 + Fpq) + 2hs\,pq(1 - F) > 0 .$$

Then the frequency $p'$ of $A$ among the survivors satisfies

$$p' - p = \frac{s\,pq\,[\,p + Fq + h(1 - F)(1 - 2p)\,]}{\bar w}.$$

For $F = 0$ this is the random-mating formula $s\,pq\,[h + p(1 - 2h)]/\bar w$, and for $F = 1$ it is
$s\,pq/\bar w$, the haploid change for relative fitness $1 + s$. The identity follows by expanding
$p' = [(p^2 + Fpq)(1 + s) + pq(1 - F)(1 + hs)]/\bar w$, using $p^2 + Fpq + pq(1 - F) = p$.

## Depends on

- [Genotype frequencies of an inbred individual](genotype-frequencies-under-inbreeding.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section V.2, equation (V-2), p. 219 (the genotype frequencies), and Section V.14,
  equation (V-48), p. 244 (mean fitness under inbreeding with arbitrary genotype fitnesses).
