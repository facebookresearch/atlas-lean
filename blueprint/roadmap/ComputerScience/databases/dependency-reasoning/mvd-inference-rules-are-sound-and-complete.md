# Inference rules for multivalued dependencies alone are sound and complete

With the rules MVD0–MVD3 of [Inference rules for functional and multivalued dependencies are sound and complete](fd-and-mvd-inference-rules-are-sound-and-complete.md),
for every set $F$ of multivalued dependencies over a finite attribute set $U$ and every multivalued dependency
$\sigma$ over $U$, $\sigma$ is derivable from $F$ by MVD0–MVD3 if and only if every relation over $U$ that satisfies
$F$ satisfies $\sigma$.

## Depends on

- [Inference rules for functional and multivalued dependencies are sound and complete](fd-and-mvd-inference-rules-are-sound-and-complete.md)
- [Join dependencies and multivalued dependencies](../dependencies-and-the-chase/multivalued-and-join-dependencies/join-dependencies-and-multivalued-dependencies.md)

## Proof depends on

- [Inference rules for functional and multivalued dependencies are sound and complete](fd-and-mvd-inference-rules-are-sound-and-complete.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Corollary 8.3.6 (p. 173).
