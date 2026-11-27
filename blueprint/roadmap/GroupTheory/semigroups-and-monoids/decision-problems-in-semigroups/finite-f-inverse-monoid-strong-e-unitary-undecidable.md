# Whether a finite F*-inverse monoid is strongly E*-unitary over finite groups is undecidable

No algorithm decides, for a finite $F^*$-inverse monoid, whether it is strongly $E^*$-unitary over finite groups, whether it is strongly $F^*$-inverse over finite groups, or whether it is a Rees quotient of a finite $F$-inverse monoid by an ideal.

An inverse monoid is ordered by its natural partial order ($s \le t$ when $s = et$ for an idempotent $e$). An inverse monoid $M$ is *$F$-inverse* if each element lies below a unique maximal element, and an inverse monoid $M$ with zero is *$F^*$-inverse* if each non-zero element lies below a unique maximal element. A Rees quotient $S/I$ of an inverse monoid $S$ by an ideal $I$ identifies all elements of $I$ to a zero. Let $M$ be an inverse monoid with zero. A partial homomorphism from $M$ to a group $G$ is a map $\phi\colon M \setminus \{0\} \to G$ with $\phi(st) = \phi(s)\phi(t)$ whenever $st \ne 0$; it is idempotent pure if only idempotents map to $1$. For a class $\mathcal{C}$ of groups, $M$ is strongly $E^*$-unitary over $\mathcal{C}$ if it admits an idempotent pure partial homomorphism to a group in $\mathcal{C}$, and strongly $F^*$-inverse over $\mathcal{C}$ if it admits a partial homomorphism to a group in $\mathcal{C}$ each of whose non-empty fibres has a maximum element. It is undecidable whether a finite $F^*$-inverse monoid is strongly $E^*$-unitary over finite groups (Theorem A.6 of the source).

It is likewise undecidable whether a finite $F^*$-inverse monoid is strongly $F^*$-inverse over finite groups (Theorem A.7), or is a Rees quotient of a finite $F$-inverse monoid by an ideal (Theorem A.8). These are Steinberg's reformulations, in an appendix, of the undecidability of developability of finite rigid pseudogroups.

## Depends on

- [Inverse monoid and inverse semigroup presentations](inverse-monoid-and-semigroup-presentations.md)
- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Developability of finite permutoids and rigid pseudogroups is undecidable](../../permutation-groups/permutoids-and-developability/permutoid-developability-undecidable.md)

## Expansion

A finite rigid pseudogroup is an inverse monoid of partial bijections of a finite set; it is developable exactly when it is strongly $E^*$-unitary over finite groups, and it has a faithful development exactly when it is strongly $F^*$-inverse over finite groups. The rigid pseudogroups produced in the proof of undecidability of finite developments have all maximal elements with the same domain, so developability and faithful developability agree for them, giving clauses 1 and 2; a proposition on ideals gives clause 3.

## Sources

- M. R. Bridson and H. Wilton, "Undecidability and the developability of permutoids and rigid pseudogroups", Forum of Mathematics, Sigma 5 (2017), article e10, https://doi.org/10.1017/fms.2017.6; read in arXiv:1405.4368v2 (with an appendix by B. Steinberg) (Theorems A.6, A.7 and A.8 of the appendix by B. Steinberg in arXiv:1405.4368v2, with the definitions of $F$-inverse, $F^*$-inverse and strongly $F^*$-inverse monoids and Proposition A.2 in that appendix).
