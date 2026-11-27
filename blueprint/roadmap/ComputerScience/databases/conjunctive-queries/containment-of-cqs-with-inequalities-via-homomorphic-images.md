# Homomorphism criterion for containment of conjunctive queries with inequalities

For conjunctive queries with inequalities $q(\bar x)$ and $q'(\bar x')$, write $q^+$ for the relational part of $q$
and $C$ for the set of constants occurring in $q$ or $q'$. Let $H_{q,q'}$ be the set of maps $h$ from the variables and
constants of $q$ to the variables of $q$ together with $C$ that are the identity on constants and satisfy
$h(v) \ne h(v')$ for every inequality $v \ne v'$ of $q$. For $h \in H_{q,q'}$, the image $h(q^+)$ is the pair of the set of atoms
$A_h = \{R_1(h(\bar u_1)), \dots, R_n(h(\bar u_n))\}$ and the output tuple $h(\bar x)$, a tableau whose summary row may
contain constants; $A_h$ is read as a database in which distinct terms denote distinct values. The image is not a
conjunctive query of the linked syntax, whose head holds only variables: for $q(x) \mathrel{:-} R(x, a)$ the map
$h(x) = a$ gives the atoms $\{R(a, a)\}$ with output tuple $(a)$, and such maps are kept. A homomorphism from $q'(\bar x')$ to $h(q^+)$ is a map from the variables and constants of
$q'$ to the terms of $A_h$ and $h(\bar x)$ together with $C$ that is the identity on constants, maps every relational atom of $q'$
to an atom of $A_h$, maps $\bar x'$ to $h(\bar x)$, and maps the two sides of every inequality of $q'$ to distinct
terms.

Then $q \subseteq q'$ if and only if, for every $h \in H_{q,q'}$, there is a homomorphism from $q'(\bar x')$ to
$h(q^+)$. The plain homomorphism criterion of the constant-free case fails here:
$\mathrm{Answer} \mathrel{:-} \mathrm{Edge}(x, y)$ is not contained in
$\mathrm{Answer} \mathrel{:-} \mathrm{Edge}(x', y'), x' \ne y'$, although the second maps to the first. The constants of
$q'$ are needed in the maps: $\mathrm{Answer} \mathrel{:-} R(x), R(y), x \ne y$ is contained in
$\mathrm{Answer} \mathrel{:-} R(z), z \ne a$, and the map $h$ with $h(x) = a$ is the image that requires choosing
$z = y$.

## Depends on

- [Conjunctive queries with inequalities](conjunctive-queries-with-inequalities.md)

## Proof depends on

- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)

## Informally uses

- [Chandra-Merlin containment criterion](../conjunctive-queries-and-the-chandra-merlin-theor/contained-iff-hom.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Example 30.7 (p. 276), the definition of $H_q$ and Theorem 30.8 (p. 277), which are stated with the constants of $q$ only.
