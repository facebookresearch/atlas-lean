# Naimark problem counterexample with a faithful tracial state

There is an infinite-dimensional unital complex C*-algebra $A$ with no norm-closed two-sided ideals besides zero and $A$, and a bounded complex-linear functional $\tau$ of norm one, nonnegative and real on $a^*a$, satisfying $\tau(ab)=\tau(ba)$ and $\operatorname{Re}\tau(a^*a)>0$ for every $a\ne0$. For every two nonzero irreducible representations by bounded operators on complex Hilbert spaces, there is a surjective complex-linear isometry intertwining every operator in the representations. Here irreducibility excludes every nonzero proper closed invariant complex subspace, and representations are not assumed unital in their definition. For no complex Hilbert space $H$ is there an injective star homomorphism from $A$ to $B(H)$ whose range consists exactly of the compact operators. The claim uses no additional set-theoretic hypothesis.

## Depends on

- [Irreducible representation](../gns-construction/cstar-irreducible-representation.md).

## Proof depends on

- Construction of the simple tracial witness and unitary equivalence of arbitrary nonzero irreducible representations of it.

## Expansion

Separate faithful trace and simplicity from representation uniqueness. Check the final obstruction against every Hilbert target, including finite dimensions; an isometric representation into all bounded operators does not identify its image with the compact operators.

## Sources

- OpenAI, [Naimark comparator, main](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Naimark.lean#L44-L52).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/297.md).
