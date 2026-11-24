# A finite abelian group is isomorphic to its dual group

Every finite abelian group $A$ is
isomorphic to its dual group, the group of characters of $A$ under pointwise multiplication,
where a character of $A$ is a map $\chi : A \to \mathbb{C}$ with $\chi(0) = 1$ and
$\chi(a + a') = \chi(a)\chi(a')$ for all $a, a' \in A$.

Proof: Use the structure theorem to write $A$ as a direct sum of finite cyclic groups,
identify each cyclic group $\mathbb{Z}/n\mathbb{Z}$ with its dual group, and transport
characters along the decomposition. This is the proof of Conrad's Theorem 3.13: the cyclic
case, then products of cyclic groups.

## Sources

- K. Conrad, Characters of finite abelian groups, https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf, Theorem 3.13.
