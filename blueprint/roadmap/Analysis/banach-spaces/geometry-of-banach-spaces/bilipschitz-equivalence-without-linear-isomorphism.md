# Quantified bi-Lipschitz equivalence without a linear isomorphism

There are separable real Banach spaces $X,Y$ and a bijection $\Psi:X\to Y$ such that for every $s,t\in X$,

$$\frac4{21}\|s-t\|\le\|\Psi(s)-\Psi(t)\|\le\frac{76}{25}\|s-t\|.$$

No bounded real-linear isomorphism with bounded inverse identifies $X$ with $Y$. The space $X$ admits a real-linear isometric embedding of $c_0(\ell_2)$, while $Y$ admits no bounded real-linear map $T:c_0(\ell_2)\to Y$ with $\|Tx\|\ge a\|x\|$ for all $x$ and some $a>0$. Here $c_0(\ell_2)$ consists of sequences of real square-summable sequences tending to zero in their Hilbert norm, equipped with the supremum norm.

## Depends on

- The real $\ell_2$ and vector-valued null sequence models and the meaning of a lower-bounded linear embedding.

## Proof depends on

- The explicit two-space construction, exact metric distortion estimates, and the obstruction to a linear copy of $c_0(\ell_2)$ in the second space.

## Expansion

Separate the lower and upper estimates for the same bijection from construction of the isometric copy and the linear exclusion. Deduce nonisomorphism by composing the copy with a hypothetical isomorphism.

## Sources

- OpenAI, [LipschitzEquivalence comparator, main](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LipschitzEquivalence.lean#L38-L40).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/324.md).
