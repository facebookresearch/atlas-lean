# Inference rules for functional and multivalued dependencies are sound and complete

Over a fixed finite attribute set $U$, consider the inference rules FD1–FD3 for functional dependencies (Armstrong's
reflexivity, augmentation and transitivity) and, for multivalued dependencies $X \twoheadrightarrow Y$ over $U$:
MVD0 (complementation) from $X \twoheadrightarrow Y$ infer $X \twoheadrightarrow U \setminus Y$; MVD1 (reflexivity)
if $Y \subseteq X$ infer $X \twoheadrightarrow Y$; MVD2 (augmentation) from $X \twoheadrightarrow Y$ infer
$XZ \twoheadrightarrow YZ$; MVD3 (transitivity) from $X \twoheadrightarrow Y$ and $Y \twoheadrightarrow Z$ infer
$X \twoheadrightarrow Z \setminus Y$; FMVD1 (conversion) from $X \to Y$ infer $X \twoheadrightarrow Y$; FMVD2
(interaction) from $X \twoheadrightarrow Y$ and $XY \to Z$ infer $X \to Z \setminus Y$. A relation over $U$ satisfies
$X \twoheadrightarrow Y$ when it equals the join of its projections on $XY$ and $X(U \setminus Y)$.

For every set $F$ of functional and multivalued dependencies over $U$ and every functional or multivalued dependency
$\sigma$ over $U$, $\sigma$ is derivable from $F$ with FD1–FD3, MVD0–MVD3, FMVD1 and FMVD2 if and only if every
relation over $U$ that satisfies $F$ satisfies $\sigma$. Unlike implication of functional dependencies, implication of
multivalued dependencies depends on $U$, which is why MVD0 mentions it.

## Depends on

- [Join dependencies and multivalued dependencies](../dependencies-and-the-chase/multivalued-and-join-dependencies/join-dependencies-and-multivalued-dependencies.md)
- [Derivability with Armstrong's axioms](../functional-dependencies/derives.md)
- [Entailment of functional dependencies](../functional-dependencies/entails.md)

## Proof depends on

- [Armstrong's theorem](../functional-dependencies/derives-iff-entails.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, the rules MVD0–MVD3, FMVD1 and FMVD2 and Theorem 8.3.5 (p. 172).
