# Dolev–Yao deduction is Horn-clause derivability

**Proposition.** For ground terms $t_1, \dots, t_n$ (the initial messages) and a ground term $t$ (the query), the [Dolev–Yao deduction](../symbolic-protocol-analysis/dolev-yao-terms-and-deduction.md) $\{t_1, \dots, t_n\} \vdash t$ holds if and only if $\mathrm{att}(t)$ is
[derivable](horn-clauses-and-derivability.md) from the facts $\mathrm{att}(t_1), \dots, \mathrm{att}(t_n)$ together with the attacker clauses, one clause
$\mathrm{att}(u_1) \wedge \dots \wedge \mathrm{att}(u_k) \to \mathrm{att}(u)$ per inference rule with premises $u_1, \dots, u_k$ and conclusion $u$. Variables occur only in these rule schemas. An initial message with variables would become a universally
quantified fact: the bare variable $x$ gives $\forall x.\ \mathrm{att}(x)$, which makes every ground $\mathrm{att}(t)$ derivable, while a compound open message such as $\mathrm{pk}(x)$ supplies
all its ground instances $\mathrm{att}(\mathrm{pk}(t))$, which the deduction from that single message does not.

## Depends on

- [Horn clauses and derivability for protocol analysis](horn-clauses-and-derivability.md)
- [Dolev–Yao terms and intruder deduction](../symbolic-protocol-analysis/dolev-yao-terms-and-deduction.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 3.2 (deduction from a set of ground messages) and Section 8.2.2, the clauses for the Dolev–Yao inference system and the statement after them.
