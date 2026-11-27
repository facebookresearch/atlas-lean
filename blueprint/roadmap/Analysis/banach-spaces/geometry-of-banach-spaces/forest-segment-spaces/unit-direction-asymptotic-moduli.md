# Unit-direction asymptotic moduli of a norm

Let $E$ be a real normed space and let $N$ be a real seminorm with comparison constants $0<\alpha\le\beta$ and $\alpha\|z\|\le N(z)\le\beta\|z\|$ for every $z\in E$. In particular $N$ is a norm equivalent to the original one. The ordinary norm is included by taking $N(z)=\|z\|$ and $\alpha=\beta=1$. Let $F$ range over closed real linear subspaces whose quotient $E/F$ is finite-dimensional. Define the one-sided and averaged midpoint moduli at a real parameter $t$ by

$$\delta_N(t)=\inf_{N(x)=1}\sup_F\inf_{y\in F,\,N(y)=1}\bigl(N(x+ty)-1\bigr),$$

$$\widetilde\delta_N(t)=\inf_{N(x)=1}\sup_F\inf_{y\in F,\,N(y)=1}\left(\frac{N(x+ty)+N(x-ty)}{2}-1\right).$$

The order of the extrema is part of the definition. Both the center and the direction have $N$-norm exactly one. The midpoint expression uses the average of the two norms, not their maximum. In the infinite-dimensional applications, every such $F$ contains unit vectors and these extrema are over nonempty bounded sets; the source uses the total real infimum and supremum.

## Depends on

- Closed subspaces, finite-dimensional quotients, real seminorms, and the real infimum and supremum.

## Sources

- OpenAI, [closed finite-codimensional subspaces and the two extrema](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Moduli.lean#L15-L50), [explicit comparison constants for an equivalent norm](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Moduli.lean#L54-L63).
