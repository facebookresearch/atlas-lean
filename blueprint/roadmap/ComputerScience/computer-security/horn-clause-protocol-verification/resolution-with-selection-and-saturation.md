# Resolution with selection and saturation

For [Horn clauses](horn-clauses-and-derivability.md) $R = H \to C$ and $R' = H' \to C'$, first renamed so that they share no variables (their variables are
universally quantified separately, so a clause resolved with itself is used in two renamed copies), and a hypothesis $F' \in H'$ unifiable with $C$ by a most general unifier $\sigma$, the *resolvent* is
$R \circ_{F'} R' = (H \cup (H' \setminus \{F'\}))\sigma \to C'\sigma$. A *selection function* maps each clause $H \to C$ to a subset of $H$; it is *basic* if it selects nothing when every hypothesis has
the form $\mathrm{att}(x)$ with $x$ a variable, and otherwise selects one hypothesis not of that form. $\mathrm{add}(R, \mathcal R)$ returns $\mathcal R$ if some clause of $\mathcal R$ subsumes $R$, and otherwise
$\{R\}$ together with the clauses of $\mathcal R$ not subsumed by $R$. $\mathrm{saturate}(\mathcal R_0)$ adds the clauses of $\mathcal R_0$ one by one with $\mathrm{add}$; then, until a fixed point, adds
$R \circ_{F'} R'$ for every clause $R$ with no selected hypothesis and every clause $R'$ with a selected hypothesis $F'$; and returns the clauses with no selected hypothesis. The backward
search $\mathrm{derivable}(F, \mathcal R_1)$ explores goals $H \to C$, starting from $F \to F$, by resolving a selected hypothesis with clauses of $\mathcal R_1$, renamed apart from the goal, discarding goals subsumed by earlier
ones, and returns the goals with no selected hypothesis.

## Depends on

- [Horn clauses and derivability for protocol analysis](horn-clauses-and-derivability.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 8.2.6, Definitions 8.3–8.4, basic selection functions, Figure 8.3 (saturation), Figure 8.4 (backward depth-first search) and Example 8.3 (resolving a clause with itself through two copies with disjoint variables).
