# Uniform sharp exponential scale of edit-distance distortion

For a finite alphabet $A$ let $E_A(d)$ be the least ℓ₁ distortion of all words over $A$ of length at most $d$, including the empty word. Use unit-cost insertions, deletions and substitutions with unrestricted intermediate lengths; the distortion of an injective map to real absolutely summable sequences is the product of the supremal forward and reverse distance ratios on distinct pairs, and the least distortion is their infimum over such maps. Put $g_b(d)=\exp(b\sqrt{\log d\log\log d})$. There are absolute $c,C>0$ and $d_0$ such that for each $d\ge d_0$: (i) $g_c(d)\le E_A(d)\le g_C(d)$ for every finite alphabet of size at least two; (ii) some finite nonempty set of binary words of one length $n\le d$ has least distortion at least $g_c(d)$; and (iii) $\sup_{a\ge2} E_{\{0,\ldots,a-1\}}(d)$ lies between these same bounds.

## Depends on

- [Unit edit costs and distance](edit-distance.md)
- Finite-word metrics, real ℓ₁ distortion and the real supremum over alphabet sizes.

## Proof depends on

- [Equal-length binary lower witness](binary-edit-distance-distortion-lower-bound.md)

## Proof outline

Separate the uniform upper embedding from transfer of the binary lower witness by isometric alphabet inclusion; prove boundedness of the alphabet supremum before applying its order laws. Keep the common constants and cutoff when combining the three statements.

- Uniform histogram embedding for arbitrary alphabets.

## Sources

- [Comparator statement: `OAI.edit_distance_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditDistance.lean#L67-L69)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/099.md)
