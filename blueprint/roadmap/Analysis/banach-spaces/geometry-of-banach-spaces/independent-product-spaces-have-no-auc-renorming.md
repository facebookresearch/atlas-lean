# Independent-product spaces have no asymptotically uniformly convex renorming

Let $\mu$ be a real probability law supported almost surely on strictly positive values, not almost surely any constant, with mean one and finite second moment. Index independent copies $W_e$ by all nonempty finite words of positive integers. Let $E_\mu$ be the closed real $L^1$ span of the product of the $W_e$ over nonempty prefixes of each finite word (the empty word contributes $1$). Then $E_\mu$ is infinite-dimensional and no real seminorm $N$ with $a\|x\|\le N(x)\le b\|x\|$ and $0<a\le b$ is AUC. AUC requires positivity at each $t>0$ of $\inf_{N(x)=1}\sup_F\inf_{y\in F,N(y)=1}(N(x+ty)-1)$ for norm-closed finite-codimensional $F$.

## Depends on

- Countable independent product law, the closed span of all path products and the one-sided cofinite modulus.

## Proof depends on

- Independence estimates for the path products proving infinite dimension and the equivalent-norm obstruction.

## Expansion

Build the product random variables and show they define $L^1$ classes, including the empty product. Separate linear independence from the one-sided modulus obstruction, preserving arbitrary norm-equivalence bounds.

## Sources

- OpenAI, [IndependentProducts comparator, main_general](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/IndependentProducts.lean#L89-L94).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
