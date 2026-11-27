# Saturation preserves derivability

**Lemma (Blanchet).** For every set $\mathcal R$ of clauses, every selection function and every closed fact $F$, $F$ is [derivable](horn-clauses-and-derivability.md) from $\mathcal R$ if and only if it is
derivable from $\mathrm{saturate}(\mathcal R)$ ([resolution with selection and saturation](resolution-with-selection-and-saturation.md)), when saturation terminates.

## Depends on

- [Resolution with selection and saturation](resolution-with-selection-and-saturation.md)
- [Horn clauses and derivability for protocol analysis](horn-clauses-and-derivability.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 8.2.6, Lemma 8.1 and the remarks on its proof.
