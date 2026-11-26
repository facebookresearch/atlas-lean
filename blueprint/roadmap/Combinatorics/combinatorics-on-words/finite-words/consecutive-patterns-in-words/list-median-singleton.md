# Median of a one-element list

For every rational $a$, the median of the one-element list $(a)$ is $a$: $\operatorname{med}((a)) = a$.

For a finite list $l$ of rationals, counted with multiplicity, let $s_0 \le s_1 \le \dots \le s_{L-1}$ be its entries in sorted order. The median of $l$ is

$$\operatorname{med}(l) = \frac{s_{\lfloor (L-1)/2 \rfloor} + s_{\lfloor L/2 \rfloor}}{2},$$

that is, the middle entry for odd $L$ and the mean of the two middle entries for even $L$; the median of the empty list is $0$.

## Sources

- Sela Fried, "Proofs of Several Conjectures From the OEIS", Journal of Integer Sequences 28 (2025), Article 25.4.3, Section 5.
