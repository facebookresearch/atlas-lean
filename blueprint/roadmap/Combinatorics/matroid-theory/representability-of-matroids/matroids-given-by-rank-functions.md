# Matroids given by rank functions

A finite matroid is a finite ground set together with a rank function on its subsets that is bounded by cardinality, monotone and submodular; the independent sets are those whose rank equals their size.

A *matroid* $M = (E, r)$ consists of a finite ground set $E$ and a rank function $r \colon \mathcal{P}(E) \to \mathbb{Z}_{\ge 0}$ such that

1. $r(A) \le |A|$ for all $A \subseteq E$;
2. $r(A) \le r(B)$ whenever $A \subseteq B \subseteq E$;
3. $r(A \cup B) + r(A \cap B) \le r(A) + r(B)$ for all $A, B \subseteq E$.

A set $A \subseteq E$ is *independent* if $r(A) = |A|$. A finite matroid is a finite object and can be given to an algorithm by the table of its rank function.

## Depends on

None.

## Proof depends on

None.

## Expansion

Rank functions determine the independent sets and conversely, so this definition is equivalent to the definitions by independent sets, bases or circuits.

## Sources

- L. Kühne and G. Yashfe, "On entropic and almost multilinear representability of matroids", *Duke Mathematical Journal* 175 (2026), no. 8, 1363–1451, doi:10.1215/00127094-2025-0047; read as arXiv:2206.03465v3, <https://arxiv.org/abs/2206.03465v3>: Definition 2.1 of arXiv:2206.03465v3.
