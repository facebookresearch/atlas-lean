# Ordered resolution with selection

Let $\succ$ be a well-founded ordering on atoms that is total on ground atoms and *stable under substitutions* ($A \succ B$ implies $A\sigma \succ B\sigma$). It is extended to literals, ground or not, by $[\neg]A \succ [\neg]B$ if $A \succ B$, and $\neg A \succ A$, and to clauses, viewed as multisets of literals, by the multiset extension; $\succeq$ is the reflexive closure. These extensions are total on ground literals and ground clauses, but in general not on non-ground ones, which is why the non-ground conditions below are stated with $\not\preceq$ and $\not\prec$. A *selection function* $\mathrm{sel}$ maps each clause to a set of occurrences of negative literals in it.

The calculus $\mathrm{Res}^\succ_{\mathrm{sel}}$ consists of the following inferences on clauses, whose variables are implicitly universally quantified.

- **Ordered resolution with selection:** from $D \vee B$ and $C \vee \neg A$, renamed apart, derive $(D \vee C)\sigma$, if (i) $\sigma$ is a most general unifier of $A$ and $B$; (ii) $B\sigma \not\preceq L\sigma$ for every literal $L$ of $D$; (iii) nothing is selected in $D \vee B$; (iv) $\neg A$ is selected in $C \vee \neg A$, or nothing is selected in $C \vee \neg A$ and $\neg A\sigma \not\prec L\sigma$ for every literal $L$ of $C$.
- **Ordered factorization with selection:** from $C \vee A \vee B$ derive $(C \vee A)\sigma$, if (i) $\sigma$ is a most general unifier of $A$ and $B$; (ii) $A\sigma \not\prec L\sigma$ for every literal $L$ of $C$; (iii) nothing is selected in $C \vee A \vee B$.

On ground clauses these conditions read: $A \succ L$ for all $L$ in $D$ and, if nothing is selected in $C \vee \neg A$, $\neg A \succeq L$ for all $L$ in $C$; and $A \succeq L$ for all $L$ in $C$ for factorization. A set $N$ of clauses is *saturated* if $\mathrm{Res}^\succ_{\mathrm{sel}}(N) \subseteq N$, where $\mathrm{Res}^\succ_{\mathrm{sel}}(N)$ is the set of conclusions of inferences with premises in $N$.

## Depends on

- [Most general unifier](../first-order-unification/is-mgu.md)
- [Unification of ranked terms through the curried encoding](../first-order-unification/unification-of-ranked-terms-through-the-curried-encoding.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.9, clause orderings, p. 66, and Section 3.13, ordering restrictions, selection functions and the calculus $\mathrm{Res}^\succ_{\mathrm{sel}}$, pp. 81–84.
