# A Tachikawa counterexample over a rational function field of characteristic two

Let $K=\operatorname{Frac}(\mathbb F_2[t_0,t_1,t_2])$. There is a finite-dimensional $K$-algebra $A$ admitting a linear isomorphism $e:A\to A^*$ with $e(ab)(c)=e(b)(ca)=e(a)(bc)$ for all $a,b,c\in A$. It has a nonprojective left module $M$ finite over $K$, with compatible $K$- and $A$-actions, for which $\operatorname{Ext}^n_A(M,M)=0$ for every $n>0$. The bimodule symmetry condition on $e$ is part of the witness.

## Depends on

- Bimodule duality of a finite-dimensional algebra and Ext in the left module category.

## Proof depends on

- The source’s symmetric algebra construction, nonprojectivity and the complete resolution controlling positive self-Ext.

## Expansion

Check the duality identities against the multiplication table and prove the required comparison with the resolution over the specified coefficient field. Do not infer symmetry just from a vector-space duality.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Tachikawa.lean#L32-L34) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Tachikawa.lean).
