# Poisson equilibrium of multiplicative mutation–selection balance

In an infinite asexual haploid population, let an individual with $k$
deleterious mutations have fitness $(1 - s)^k$, $0 < s < 1$, and let each offspring acquire a $\mathrm{Poisson}(U)$ number of
new mutations, independently, with no back mutation. If the mutation counts have law $\mathrm{Poisson}(\lambda)$, selection
turns this into $\mathrm{Poisson}(\lambda (1 - s))$, since

$$\frac{e^{-\lambda} \lambda^k (1 - s)^k / k!}{\sum_j e^{-\lambda} \lambda^j (1 - s)^j / j!} = \frac{e^{-\lambda(1-s)} (\lambda(1 - s))^k}{k!},$$

and new mutation turns $\mathrm{Poisson}(\lambda(1 - s))$ into $\mathrm{Poisson}(\lambda(1 - s) + U)$. Hence $\mathrm{Poisson}(U/s)$ is a fixed point of
selection followed by mutation, at which the mean fitness is

$$\bar w = \mathbb E (1 - s)^K = e^{-sU/s} = e^{-U},$$

independent of $s$, and the mutation-free class has frequency $e^{-U/s}$. This is the many-locus form of the
Haldane–Muller principle that the [load](load-mult-at-equilibrium.md) depends on the mutation rate, not on the selection coefficient.
For a sexual population the same fixed point holds only if the mutation-count distribution stays Poisson through
recombination, as under linkage equilibrium across very many loci; that reduction is not proved here.

## Depends on

- [Haldane–Muller load](load-mult-at-equilibrium.md)

## Proof depends on

- [Generating function of a sum of independent variables](../../../Probability/characteristic-functions/probability-generating-functions/pgf-add-of-indep-fun.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section III.7 (the Haldane–Muller principle: the mean fitness at mutation–selection equilibrium is depressed by the mutation rate, independently of the selection coefficient). The Poisson fixed point is derived above.
