# The Horn-clause secrecy analysis is sound, and complete for ground goals

**Theorem (Blanchet).** Let $\mathcal R$ be a set of [Horn clauses](horn-clauses-and-derivability.md) and $F$ a fact, and suppose saturation terminates. If
$\mathrm{derivable}(F, \mathrm{saturate}(\mathcal R)) = \emptyset$, then no instance of $F$ is derivable from $\mathcal R$; in particular a term $t$ with $\mathrm{att}(t)$ not derivable is secret. If the
selection function is basic, $F$ is ground and $\mathcal R$ contains the fact $\mathrm{att}(a[])$ for some name $a[]$ (the attacker knows at least one name), then $F$ is derivable from $\mathcal R$ if and only if $\mathrm{derivable}(F, \mathrm{saturate}(\mathcal R)) \ne \emptyset$.

## Depends on

- [Resolution with selection and saturation](resolution-with-selection-and-saturation.md)
- [Horn clauses and derivability for protocol analysis](horn-clauses-and-derivability.md)

## Proof depends on

- [Saturation preserves derivability](saturation-preserves-derivability.md)
- [Backward search finds the derivable instances](backward-search-finds-derivable-instances.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 8.2.2 (the assumption that the attacker knows a name $a[]$, with the clause $\mathrm{att}(a[])$) and Section 8.2.6, the argument after Lemma 8.2 combining Lemmas 8.1 and 8.2, which uses $\mathrm{att}(a[])$ to derive the remaining hypotheses $\mathrm{att}(x)$.
