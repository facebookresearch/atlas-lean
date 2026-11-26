# Universal bound for amplified von Neumann algebra commutators

There is a single real $C\geq0$ such that for every complex Hilbert space $H$, von Neumann algebra $P\subseteq\mathcal B(H)$, operator $Y\in\mathcal B(H)$, and finite $n\geq0$, the following holds. For $X=(X_{ij})\in M_n(P)$ acting on the Hilbert direct sum $H^n$ by matrix multiplication, and $Y^{(n)}$ acting diagonally there, one has

$$
\|Y^{(n)}X-XY^{(n)}\|\leq C\,\|[Y,\cdot]\!:\!P\to\mathcal B(H)\|\,\|X\|.
$$

The middle norm is the supremum of $\|Ya-aY\|$ over $a\in P$ of operator norm at most one. At $n=0$ the inequality is zero on both sides, so the positive-size version is equivalent. Neither separability nor a type restriction is imposed on $P$.

## Depends on
The concrete operator norm on the Hilbert direct sum and the restricted inner derivation on $P$.

## Proof depends on
Amplification control independent of the matrix size and the type decomposition of the von Neumann algebra.

## Expansion
State the row, cyclic and corner estimates separately, assemble the uniform factor case, and justify the extension to all von Neumann algebras. Verify the scalar derivation norm is the unit-ball supremum, not the norm over all of $\mathcal B(H)$.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KadisonSimilarity.lean#L106-L109) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/288.md).
- OpenAI, [positive-size unit-ball-supremum version](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/UniformCommutator.lean#L10-L35).
