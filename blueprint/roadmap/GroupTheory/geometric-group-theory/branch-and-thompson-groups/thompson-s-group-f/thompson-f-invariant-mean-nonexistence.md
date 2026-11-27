# Thompson’s group F has no invariant mean

Let $F$ be the increasing homeomorphisms of $[0,1]$ that are affine on a finite consecutive partition with dyadic endpoints $0=t_0<\cdots<t_r=1$ and slopes $2^k$ with $k\in\mathbb Z$. Dyadic means $a/2^m$ with $a\in\mathbb Z,m\ge0$. There is a group structure on $F$ with $(hg)(x)=h(g(x))$, and for this structure no real linear functional on bounded real functions on $F$ is simultaneously positive on pointwise nonnegative functions, normalized to $1$ on the constant-one function, and invariant under $f(g)\mapsto f(hg)$ for every $h\in F$. This is a mean-exclusion statement, not a quantitative isoperimetric bound.

## Depends on

- [Standard presentation of Thompson’s F](thompson-f.md) and its bridge to dyadic PL homeomorphisms; left invariance on bounded functions.

## Proof depends on

- Composition and inversion closure on the PL model and the source obstruction to an invariant mean.

## Expansion

Prove the PL closure and compare its group law to the presentation model. Transport the mean obstruction with consistent multiplication orientation; it is not the non-Howson-property theorem.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThompsonNonamenability.lean#L78-L84) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThompsonNonamenability.lean).
