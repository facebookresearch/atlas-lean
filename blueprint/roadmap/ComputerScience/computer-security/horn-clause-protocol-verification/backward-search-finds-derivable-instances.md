# Backward search finds the derivable instances

**Lemma (Blanchet).** Let $F_0$ be a ground instance of a fact $F$. Then $F_0$ is [derivable](horn-clauses-and-derivability.md) from $\mathcal R_1$ if and only if some clause $H \to C$ in
$\mathrm{derivable}(F, \mathcal R_1)$ ([resolution with selection and saturation](resolution-with-selection-and-saturation.md)) and some substitution $\sigma$ have $F_0 = C\sigma$ with every fact of $H\sigma$ derivable from
$\mathcal R_1$.

## Depends on

- [Resolution with selection and saturation](resolution-with-selection-and-saturation.md)
- [Horn clauses and derivability for protocol analysis](horn-clauses-and-derivability.md)

## Sources

- B. Blanchet, "Using Horn clauses for analyzing security protocols", in V. Cortier and S. Kremer (eds.), *Formal Models and Techniques for Analyzing Security Protocols*, Cryptology and Information Security Series 5, IOS Press, 2011, author copy at <https://bblanche.gitlabpages.inria.fr/publications/BlanchetBook09.pdf>: Section 2.1, Lemma 2 (correctness of derivable), proved in Section 2.2.
- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 8.2.6, Lemma 8.2.
