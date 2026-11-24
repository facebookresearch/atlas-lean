# Mean fitness is linear in the inbreeding coefficient

Let a biallelic locus with allele frequency $p$ ($q = 1 - p$) have the genotype frequencies
$p^2 + Fpq$, $2pq(1 - F)$, $q^2 + Fpq$ of
[an individual with inbreeding coefficient $F \in [0, 1]$](genotype-frequencies-under-inbreeding.md),
and let the genotypes $AA$, $Aa$, $aa$ have values $w_{AA}, w_{Aa}, w_{aa}$ (fitnesses or genotypic
values). Then the population mean is

$$\bar w(F) = \bar w(0) - F\,pq\,(2 w_{Aa} - w_{AA} - w_{aa}),$$

where $\bar w(0) = p^2 w_{AA} + 2pq\,w_{Aa} + q^2 w_{aa}$. The mean is linear in $F$ and, for
$0 < p < 1$ and $F > 0$, decreases with inbreeding exactly when the heterozygote exceeds the average of
the homozygotes. In particular:

- with Falconer's genotypic values $a$, $d$, $-a$, the inbreeding depression is
  $\bar w(0) - \bar w(F) = 2pqdF$;
- with fitnesses $1$, $1 - hs$, $1 - s$, $\bar w(F) = \bar w(0) - F\,pq\,s(1 - 2h)$, so for $s > 0$
  inbreeding lowers mean fitness iff $h < 1/2$.

## Depends on

- [Genotype frequencies of an inbred individual](genotype-frequencies-under-inbreeding.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section V.14 "The Effects of Inbreeding", equation (V-48), p. 244.
