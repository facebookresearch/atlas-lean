# Spherical extension in the strict mixed-norm range

Let $n\geq2$ and let $\sigma$ be surface measure on the Euclidean unit sphere (the polar measure from Lebesgue volume), viewed as a measure on $\mathbb R^n$ by inclusion. Fix $1<a\leq\infty$ and real $b$ with $b>2n/(n-1)$ and $b>((n+1)/(n-1))a'$; here $a'=a/(a-1)$ for finite $a$ and $a'=1$ for $a=\infty$. For complex $g\in L^a(\sigma)$ define $Eg(x)=\int e^{i x\cdot\omega}g(\omega)\,d\sigma(\omega)$. Then $Eg\in L^b(\mathbb R^n)$ and $\|Eg\|_b\leq C\|g\|_{L^a(\sigma)}$ for some $C>0$ depending only on $n,a,b$.

## Depends on

Polar surface measure, including its pushforward to ambient space, and the angular extension integral for ambient measurable representatives.

## Proof depends on

The spherical cap estimates and their assembly in the strict mixed range; existence of the integral at each point uses finite surface measure and $a>1$.

## Expansion

Establish the localized extension bounds with their cap scales and sum the pieces using both strict inequalities. Keep the finite $b$ condition and treat $a=\infty$ with its own conjugate-exponent convention.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LocalSmoothing.lean#L108-L118) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/079.md).
