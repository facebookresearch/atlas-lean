# Tensor-field classification of Euclidean Ramsey configurations

Let $s\ge2,d\ge1$ and let $a_0,\ldots,a_{s-1}$ be distinct points affinely spanning $\mathbb R^d$. Call $a$ Ramsey if, for each integer $r\ge2$, there is $D\ge1$ such that every $r$-colouring of $\mathbb R^D$ has a monochromatic configuration with exactly its labelled pairwise distances. Put $K=\mathbb Q(a_{ij}:i,j)$, $R=K\otimes_{\mathbb Q} K$, $u_i=(1,a_{i1},\ldots,a_{id})$ and let $\mu:R\to K$ be the multiplication map. Then $a$ is Ramsey if and only if there is a $(d+1)$-square matrix $P$ over $R$ such that

$$
\sum_{\alpha,\beta}(u_{i\alpha}\otimes1)P_{\alpha\beta}(1\otimes u_{i\beta})=0\quad\text{for every }i,
$$

and $\mu(P_{\alpha\beta})=\delta_{\alpha\beta}$ for $1\le\alpha,\beta\le d$. The augmented constant coordinate is excluded only from the latter condition.

## Depends on

- [Indexed Euclidean Ramsey configurations](is-euclidean-ramsey.md)
- Labelled Euclidean Ramsey configurations, the coordinate field generated over the rationals, and their tensor-algebra evaluations.

## Proof depends on

- Necessity via a finite-colouring obstruction to the evaluation constraints, sufficiency via realizing the tensor certificate by monochromatic congruences, and coefficient descent to the generated field.

## Expansion

Separate both directions and the affine-span and field-descent prerequisites. The tensor coefficient condition is not a real quadratic equation: retain each tensor factor and the multiplication map only on the spatial block.

## Sources

- [Comparator statement: `OAI.EuclideanRamsey.classification`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EuclideanRamsey.lean#L42-L47)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/172.md)
