# Characters of a product of abelian groups

For all abelian groups $A$ and $B$, the group of
characters of $A \times B$ is isomorphic to the product of the character groups of $A$ and $B$.
Here a character of $A$ is a map $\chi : A \to \mathbb{C}$ with $\chi(0) = 1$ and
$\chi(a + a') = \chi(a)\chi(a')$ for all $a, a' \in A$, and the characters of $A$ form a group
under pointwise multiplication.

Proof: Restrict a character along the two coordinate inclusions, with inverse
$(\chi_1, \chi_2) \mapsto ((x, y) \mapsto \chi_1(x)\chi_2(y))$. Conrad's Lemma 3.12 uses the
same restriction map for finite groups and concludes by counting; the explicit
inverse removes the finiteness assumption.

## Sources

- K. Conrad, Characters of finite abelian groups, https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf, Lemma 3.12.
