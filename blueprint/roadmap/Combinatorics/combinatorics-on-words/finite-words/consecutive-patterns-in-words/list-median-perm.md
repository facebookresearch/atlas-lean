# The median of a list depends only on its multiset

If two finite lists $l$ and $l'$ of rationals are permutations of each other, then $\operatorname{med}(l) = \operatorname{med}(l')$: the median depends only on the multiset of entries.

For a finite list $l$ of rationals, counted with multiplicity, let $s_0 \le s_1 \le \dots \le s_{L-1}$ be its entries in sorted order. The median of $l$ is

$$\operatorname{med}(l) = \frac{s_{\lfloor (L-1)/2 \rfloor} + s_{\lfloor L/2 \rfloor}}{2},$$

that is, the middle entry for odd $L$ and the mean of the two middle entries for even $L$; the median of the empty list is $0$.

## Sources

- Sela Fried, "Proofs of Several Conjectures From the OEIS", Journal of Integer Sequences 28 (2025), Article 25.4.3, Section 5 (median of a multiset).
