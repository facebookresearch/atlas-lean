# Optimal contributions under independent parental sampling

Let $n\ge1$ candidate parents have fixed [gene-dropping kinships](../quantitative-genetics/pedigree-kinship-and-inbreeding/gene-drop-kinship.md)
$F_{ij}$, including diagonal self-kinships. Choose each offspring's two
parents $I,J$ independently with the same distribution $c_i\ge0$,
$\sum_i c_i=1$, with replacement. This model permits selfing and does not
impose separate sex roles. Conditional on parents $i,j$, the offspring's
inbreeding coefficient is $F_{ij}$. Thus

$$\mathbb E[F_{\rm offspring}]=\sum_{i,j}c_ic_jF_{ij}=c^\top Fc.$$

The matrix is kinship, not the additive relationship matrix $2F$.
For specified estimated breeding values $\hat a\in\mathbb R^n$ and a real
bound $C$, put

$$\mathcal C=\{c\in\mathbb R^n:c_i\ge0,\ \sum_i c_i=1,\ c^\top Fc\le C\}.$$

If $\mathcal C$ is nonempty, $c^\top\hat a$ has a maximum on $\mathcal C$.
The set is nonempty exactly when $C$ is at least the minimum of $c^\top Fc$
on the simplex; that minimum exists. This maximizes the mean parental
estimated breeding value subject to the stated expected-inbreeding bound.
If an additive prediction model assigns offspring of $i,j$ the predicted
value $(\hat a_i+\hat a_j)/2$, its mean predicted offspring value is also
$c^\top\hat a$. Equality with the true expected genetic level requires an
additional calibrated inheritance/prediction assumption, not just arbitrary
estimates $\hat a$.

## Depends on

- [Gene-dropping kinship](../quantitative-genetics/pedigree-kinship-and-inbreeding/gene-drop-kinship.md)

## Proof depends on

- [Inbreeding is the kinship of the parents](../quantitative-genetics/pedigree-kinship-and-inbreeding/inbreeding-of-parents-eq-some.md)

## Expansion

Condition on the ordered pair $(I,J)$ and use its probability $c_ic_j$.
The simplex is compact, $c\mapsto c^\top Fc$ is continuous, and its sublevel
set is closed; hence the feasible set is compact. The continuous linear
objective attains its maximum when that set is nonempty. No uniqueness is
asserted. Separate-sex parent distributions, assortative or constrained
mating, integer offspring counts and realized rather than expected
inbreeding are different optimization problems; their coefficients cannot
be silently substituted into this model.

## Sources

- T. H. E. Meuwissen, "Maximizing the response of selection with a predefined rate of inbreeding", Journal of Animal Science 75 (1997), 934–940, <https://doi.org/10.2527/1997.754934x>, abstract (optimal contributions with constrained coancestry). The independent-with-replacement sampling model, prediction qualification and compactness proof are explicit above; no claim to the full sex-constrained breeding program is made.
