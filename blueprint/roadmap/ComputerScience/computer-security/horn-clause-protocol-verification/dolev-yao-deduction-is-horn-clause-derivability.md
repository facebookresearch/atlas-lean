# Dolev–Yao deduction is Horn-clause derivability

**Proposition.** For terms $t_1, \dots, t_n, t$, the [Dolev–Yao deduction](../symbolic-protocol-analysis/dolev-yao-terms-and-deduction.md) $\{t_1, \dots, t_n\} \vdash t$ holds if and only if $\mathrm{att}(t)$ is
[derivable](horn-clauses-and-derivability.md) from the facts $\mathrm{att}(t_1), \dots, \mathrm{att}(t_n)$ together with the attacker clauses, one clause
$\mathrm{att}(u_1) \wedge \dots \wedge \mathrm{att}(u_k) \to \mathrm{att}(u)$ per inference rule with premises $u_1, \dots, u_k$ and conclusion $u$.

## Depends on

- [Horn clauses and derivability for protocol analysis](horn-clauses-and-derivability.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 8.2.2, the clauses for the Dolev–Yao inference system and the statement after them.
