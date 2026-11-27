# Quadratic row independence implies a spherical configuration is Ramsey

Let $a_i\in\mathbb R^d$ be a finite injective family affinely spanning $\mathbb R^d$, all at the same real distance from some center. Write $K=\mathbb Q(a_{ij}:i,j)$ and $u_i=(1,a_{i1},\ldots,a_{id})$. Suppose the $s$ rows $(u_{i\alpha}u_{i\beta})_{0\le\alpha,\beta\le d}$ of ordered quadratic evaluations are linearly independent over $K$. Then for each $r\ge2$ there is $D\ge1$ such that every $r$-colouring of $\mathbb R^D$ contains a monochromatic configuration with the same labelled distances as $a$.

## Depends on

- [Indexed Euclidean Ramsey configurations](is-euclidean-ramsey.md)
- Generated coordinate field, full affine span, common-radius sphere, and independence of augmented quadratic evaluation rows.

## Proof depends on

- [Euclidean Ramsey sufficiency of the tensor condition](euclidean-ramsey-tensor-field-criterion.md)

## Proof outline

Separate the row-rank linear algebra from the Ramsey direction and handle dimension zero and singleton separately if needed; there is no explicit lower bound on the dimension or family size in this comparator.

- From independence and cosphericity construct a tensor-field certificate; apply the sufficiency theorem.

## Sources

- [Comparator statement: `OAI.EuclideanRamsey.spherical_quadraticIndependent_ramsey_all`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EuclideanRamseyQuadratic.lean#L31-L39)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/172.md)
