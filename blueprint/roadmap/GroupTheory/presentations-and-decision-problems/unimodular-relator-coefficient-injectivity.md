# Coefficient injectivity for a unimodular one-relator quotient

Let $A$ be any group and $w\in A*\mathbb Z$. Its exponent sum is the image of $w$ under the projection killing $A$ and sending the infinite-cyclic generator to $1\in\mathbb Z$. If the exponent sum is $1$ or $-1$, the composite $A\to A*\mathbb Z\to(A*\mathbb Z)/\langle\!\langle w\rangle\!\rangle$ is injective. The quotient is by the normal closure of the single relator. No torsion restriction on $A$ is imposed.

## Depends on

- Free-product inclusions and projection, and the normal-closure quotient.

## Proof depends on

- Normalization to cyclic finite position data with unit exponents, and the relator-ribbon lemma that the coefficient subgroup meets the normal closure trivially.

## Expansion

Prove the normalization preserves both the full relator and its exponent sum. Port the finite ribbon statement and its normal-closure-to-coefficient conclusion, then identify this with injectivity of the canonical map.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Kervaire.lean#L31-L34) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Kervaire.lean).
