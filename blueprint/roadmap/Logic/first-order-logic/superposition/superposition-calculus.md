# Superposition calculus

Work with clauses over a signature whose only predicate is equality: a clause is a finite multiset of literals $s \approx t$ and $s \not\approx t$, with $\approx$ symmetric and variables implicitly universally quantified; a predicate atom $P(t_1, \dots, t_n)$ is encoded as $f_P(t_1, \dots, t_n) \approx \mathrm{true}$ for a new function symbol $f_P$ and constant $\mathrm{true}$. The inference rules are:

- **Positive superposition:** from $D' \vee t \approx t'$ and $C' \vee s[u] \approx s'$ derive $(D' \vee C' \vee s[t'] \approx s')\sigma$;
- **Negative superposition:** from $D' \vee t \approx t'$ and $C' \vee s[u] \not\approx s'$ derive $(D' \vee C' \vee s[t'] \not\approx s')\sigma$;
- **Equality resolution:** from $C' \vee s \not\approx s'$ derive $C'\sigma$, where $\sigma$ is a most general unifier of $s$ and $s'$;
- **Equality factoring:** from $C' \vee s' \approx t' \vee s \approx t$ derive $(C' \vee t \not\approx t' \vee s \approx t')\sigma$, where $\sigma$ is a most general unifier of $s$ and $s'$;

where in the superposition rules $\sigma$ is a most general unifier of $t$ and $u$ and $u$ is not a variable.

Let $\succ$ be a [reduction ordering](../term-rewriting/reduction-ordering.md) that is total on ground terms. A positive literal $s \approx t$ is assigned the multiset $\{s, t\}$ and a negative literal $s \not\approx t$ the multiset $\{s, s, t, t\}$; literals are compared by the multiset extension $\succ_L$ of $\succ$ on these multisets, and clauses by the multiset extension $\succ_C$ of $\succ_L$. An inference is performed only if, after applying the unifier to the premises: in superposition inferences the left premise is not greater than or equal to the right one; the last displayed literal of each premise is maximal in it, and strictly maximal for positive literals in superposition inferences; and in these literals the left-hand side is neither smaller than nor equal to the right-hand side, except in equality resolution.

## Depends on

- [Reduction ordering](../term-rewriting/reduction-ordering.md)
- [Unification returns a most general unifier](../first-order-unification/is-mgu-unify.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 3.2, the encoding of predicates, p. 49, and Section 3.3, inference rules, orderings and ordering restrictions, pp. 52–53.
