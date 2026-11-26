# Weakest-link product theorem (conditional)

Let $n \in \mathbb{N}$ and let $\mathrm{system}, S : \mathbb{R} \to \mathbb{R}$ and $\mathrm{link}_i : \mathbb{R} \to \mathbb{R}$ ($i \in \mathbb{N}$) be arbitrary functions. Suppose the system survival is the product of the link survivals,

$$\mathrm{system}(x) = \prod_{i=0}^{n-1} \mathrm{link}_i(x) \quad \text{for all } x,$$

and every link has survival $S$: $\mathrm{link}_i(x) = S(x)$ for all $i < n$ and all $x$. Then $\mathrm{system}(x) = S(x)^n$ for every $x$. The product hypothesis encodes independence of the links; no form of the hazard is assumed.
