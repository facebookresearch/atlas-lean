# Horn clauses and derivability for protocol analysis

Terms are built from variables, function symbols and *names with arguments* $a[t_1, \dots, t_n]$, which model fresh values. The single predicate $\mathrm{att}(t)$ states that the attacker
knows $t$. A *Horn clause* $H \to C$, written $H_1 \wedge \dots \wedge H_n \to C$, has a set $H$ of facts as hypotheses and a fact $C$ as conclusion, its variables universally quantified. A clause
$H_1 \to C_1$ *subsumes* $H_2 \to C_2$, written $H_1 \to C_1 \sqsupseteq H_2 \to C_2$, if $C_1\sigma = C_2$ and $H_1\sigma \subseteq H_2$ for some substitution $\sigma$. A closed fact $f$ is *derivable* from a set $\mathcal R$
of clauses if there is a finite tree labelled by facts, with root $f$, such that for each node labelled $f_0$ with children labelled $f_1, \dots, f_n$ some $R \in \mathcal R$ has
$R \sqsupseteq \{f_1, \dots, f_n\} \to f_0$.

The attacker's capabilities are clauses such as $\mathrm{att}(x) \wedge \mathrm{att}(y) \to \mathrm{att}(\langle x, y\rangle)$, $\mathrm{att}(\langle x, y\rangle) \to \mathrm{att}(x)$ and
$\mathrm{att}(\mathrm{senc}(x, y)) \wedge \mathrm{att}(y) \to \mathrm{att}(x)$, one per [Dolev–Yao inference rule](../symbolic-protocol-analysis/dolev-yao-terms-and-deduction.md), with $\mathrm{att}(t)$ for each term $t$ the
attacker knows initially, which by convention include at least one name $a[]$, so that the clause $\mathrm{att}(a[])$ is present; protocol steps become clauses from received to sent messages. A term $t$ is secret when $\mathrm{att}(t)$ is not derivable.

## Depends on

- [Dolev–Yao terms and intruder deduction](../symbolic-protocol-analysis/dolev-yao-terms-and-deduction.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Sections 8.2.1–8.2.5, Definitions 8.1 (subsumption) and 8.2 (derivability), and Section 8.2.2 (the attacker always knows at least one name $a[]$).
