# Euclidean Steinitz–Bergström bound with one constant

There is one real $C$ with these two properties for all integers $d,N\geq1$ and every ordered family $v_0,\dots,v_{N-1}$ in the Euclidean unit ball of $\mathbb R^d$. First, there are signs $\varepsilon_i\in\{-1,1\}$ such that $|\sum_{i<k}\varepsilon_i v_i|\leq C\sqrt d$ for every $0\leq k\leq N$. Second, when $\sum_i v_i=0$, there is a permutation $\pi$ of the $N$ indices such that $|\sum_{i<k}v_{\pi(i)}|\leq C\sqrt d$ on the same range. The vectors may repeat or be zero; the signing need not be online.

## Depends on
Finite indexed vector sequences, Euclidean norm, and prefixes including the empty prefix and the whole family.

## Proof depends on
A simultaneous signed-prefix selection bound and a transference argument from sign control to reordering zero-sum families.

## Expansion
State the Gaussian section and adaptive linear-equation estimate for the signing step; then separate the signed-prefix estimate from the transference to permutations. Account for the constant in both conclusions with a common absolute choice.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SteinitzBergstrom.lean#L24-L26) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/097.md).
