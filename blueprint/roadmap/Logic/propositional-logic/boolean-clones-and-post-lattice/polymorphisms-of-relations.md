# Polymorphisms of relations

Let $D$ be a set, $R \subseteq D^{I}$ a relation with coordinate set $I$, and $f : D^{J} \to D$ an operation of arity $J$. Then $f$ *preserves* $R$ (is a *polymorphism* of $R$) if for every family $(t_j)_{j \in J}$ of tuples in $R$, the tuple obtained by applying $f$ coordinatewise, $\big(f((t_j(i))_{j\in J})\big)_{i \in I}$, again lies in $R$. An operation is a polymorphism of a set $\Gamma$ of relations if it preserves every member of $\Gamma$; $\mathrm{Pol}(\Gamma)$ denotes the set of all polymorphisms.

## Sources

- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009).
- P. Jeavons, D. Cohen and M. Gyssens, "Closure Properties of Constraints", Journal of the ACM 44(4), 527–548, 1997.
