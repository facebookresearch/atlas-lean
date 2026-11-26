# Precise predicates

A predicate $p \subseteq \Sigma$ over a [separation algebra](separation-algebras.md) is *precise* if every state $\sigma$ has at most one substate $\sigma_p \preceq \sigma$ with $\sigma_p \in p$. In the heap model a points-to predicate $l \mapsto v$, true only of the one-cell heap mapping $l$ to $v$, and a separating conjunction of such predicates are precise, while the disjunction $l_0 \mapsto v_0 \vee l_1 \mapsto v_1$ of two of them, for distinct locations, is not.

## Depends on

- [Separation algebras](separation-algebras.md)

## Sources

- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007; extended version of April 13, 2007, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-long.pdf>, Section 2, Definition 3 and the examples after it.
