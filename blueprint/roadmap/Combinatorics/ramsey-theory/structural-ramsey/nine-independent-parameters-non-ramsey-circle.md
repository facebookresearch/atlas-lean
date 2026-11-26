# Nine algebraically independent circle parameters give a non-Ramsey configuration

Let $t_0,\ldots,t_8\in\mathbb R$ be algebraically independent over $\mathbb Q$, and put $a_i=((1-t_i^2)/(1+t_i^2),2t_i/(1+t_i^2))$. The points $a_i$ are distinct and have distance one from the origin. This configuration is not Euclidean Ramsey: for some number $r\ge2$, every positive Euclidean dimension admits an $r$-coloring without a monochromatic distance-preserving copy of it.

## Depends on

- [Indexed Euclidean Ramsey configurations](is-euclidean-ramsey.md)
- Algebraic independence, stereographic rational parametrization, and all-dimensions Euclidean Ramsey obstruction.

## Proof depends on

- [Euclidean Ramsey necessity of the tensor condition](euclidean-ramsey-tensor-field-criterion.md)

## Proof outline

Check denominators never vanish and recover $t$ from a point on the image, which omits $(-1,0)$. State the tensor obstruction independently and use the necessity direction of the classification. Do not identify this with the twelve-point construction.

- Injectivity and norm identity on the parametrization, and a nonzero rank or tensor obstruction from algebraic independence.

## Sources

- [Comparator statement: `OAI.EuclideanRamsey.NineStatement.nine_circle_configuration`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EuclideanRamseyNine.lean#L24-L32)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/172.md)
