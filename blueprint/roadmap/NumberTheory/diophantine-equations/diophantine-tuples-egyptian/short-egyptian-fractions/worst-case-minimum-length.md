# Double-logarithmic order of the worst-case minimum Egyptian length

Let $L(a,b)$ be the infimum of the natural lengths $k$ of tuples in $\mathcal E_k^{<}$ whose
reciprocals sum in $\mathbb Q$ to $a/b$, where $\mathcal E_k^{<}$ is the existing strictly increasing
Egyptian denominator tuple model with all denominators at least two. Put
$M(b)=\max_{1\le a<b}L(a,b)$, using zero for an empty maximum.
There exist real constants $c_1,c_2>0$ and a natural $b_0$ such that for every natural $b\ge b_0$,

$$
c_1\log\log b\le M(b)\le c_2\log\log b.
$$

One may take $b_0\ge2$: the list-based source statement explicitly includes that restriction and
uses the same minimum lengths after translating lists to tuples. No coprimality restriction is
placed on the numerator $a$ in the maximum.

## Depends on

- [Strictly increasing Egyptian denominator tuples](../egyptian-fraction-underapproximations/is-strict-egyptian.md)

## Proof depends on

- [Attainment and characterization of the minimum length](minimum-expansion-length.md)

## Expansion

Record the corresponding lower-bound examples and the constructive upper bound for all $1\le a<b$. Isolate the uniform residue-density descent and the divisor-moment estimates used to bound the worst-case length above. Prove that the finite supremum over positive numerators agrees in both source models.

## Sources

- [EgyptianFractions.lean — `main_double_log_order`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L57-L63)
- [ShortEgyptianFractions.lean — `main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ShortEgyptianFractions.lean#L17-L24)
- [Source exact-expansion and maximum definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L11-L23)
- [List expansion and length definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ShortEgyptianFractions.lean#L7-L15)
