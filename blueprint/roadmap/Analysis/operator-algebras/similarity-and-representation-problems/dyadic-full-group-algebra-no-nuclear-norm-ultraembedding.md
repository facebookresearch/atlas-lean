# A dyadic full group algebra with no nuclear norm-ultrapower embedding

Let $G=\mathbb Z[1/2]^3\rtimes(\operatorname{SL}_3(\mathbb Z)\times\mathbb Z)$, with $(M,k)$ acting by $v\mapsto 2^kMv$. There exists a nonzero separable unital complex $C^*$-algebra $A$ and a unitary representation $\iota$ of $G$ with dense complex span, universal for unitary representations into nonzero unital complex $C^*$-algebras via unique unital star homomorphisms. This specifies the full group algebra, not the reduced one. For every nonzero unital nuclear $B$ and free ultrafilter $\omega$ on $\mathbb N$, there is no injective unital star homomorphism $A\to B^\omega$, where $B^\omega$ is the quotient of norm-bounded sequences by sequences whose norms converge to zero along $\omega$. Nuclearity is equality of the spatial and commuting-representation tensor norms with every second complex $C^*$-algebra, allowing nonunital second algebras. In addition there exists a nonzero unital universal algebra $O$ on two isometries $s_1,s_2$ with $s_1s_1^*+s_2s_2^*=1$, universal for pairs satisfying these relations, and no such embedding $A\to O^\omega$ exists for any free $\omega$. The comparator uses small type universes for its explicit target.

## Depends on
The exact semidirect product action, universal full group and Cuntz algebras, and the operator-norm rather than tracial ultrapower.

## Proof depends on
Construction and universal properties of the two algebras, identification of the obstruction surviving the norm quotient, and the Cuntz case (including nuclearity if deduced from the general obstruction).

## Expansion
Construct and check the full completion from the universal representation norm; isolate the obstruction to injectivity over every target and free ultrafilter. Verify the Cuntz relations, their universal property, and specialization to the Cuntz algebra without adding hypotheses to the claimed witness.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/NuclearUltrapower.lean#L206-L210) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/292.md).
