# Closure properties of polymorphisms

For every relation $R$ on $D$: every projection $(x_j)_{j} \mapsto x_{j_0}$ preserves $R$; if $f$ of arity $J$ preserves $R$ and $g_j$ of arity $K$ preserve $R$ for all $j \in J$, then the superposition $x \mapsto f((g_j(x))_{j})$ preserves $R$; and the set of relations preserved by a fixed operation $f$ is closed under arbitrary intersections, variable substitutions (preimages under coordinate maps) and projections onto subsets of coordinates. Hence $\mathrm{Pol}(\Gamma)$ is a clone for every $\Gamma$, and polymorphisms of $\Gamma$ preserve every relation primitive-positively definable from $\Gamma$. A constant operation with value $c$ preserves $R$ iff $R$ is empty or contains the constant tuple $c$.

## Proof sketch

Each claim unfolds to coordinatewise application commuting with the operation in question.

## Depends on

- [Polymorphisms of relations](polymorphisms-of-relations.md)
- [Boolean clones](boolean-clones.md)

## Sources

- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009).
- D. Geiger, "Closed Systems of Functions and Predicates", Pacific Journal of Mathematics 27(1), 95–100, 1968.
