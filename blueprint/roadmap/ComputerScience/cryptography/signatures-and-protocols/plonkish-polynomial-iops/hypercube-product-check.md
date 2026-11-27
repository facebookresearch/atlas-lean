# Product check over the Boolean hypercube with an auxiliary multilinear tree

Let $f:\{0,1\}^{\mu}\to\mathbb{F}$ have multilinear extension $\widetilde{f}$. Then $\prod_{x\in\{0,1\}^{\mu}}f(x)=s$ iff there is a multilinear $\widetilde{v}$ in $\mu+1$ variables with $\widetilde{v}(0,x)=\widetilde{f}(x)$, $\widetilde{v}(1,\dots,1,0)=s$, and, for all $x\in\{0,1\}^{\mu}$,

$$
\widetilde{v}(1,x)=\widetilde{v}(x,0)\cdot\widetilde{v}(x,1).
$$

The last identity is a degree-$2$ zero-check over the hypercube, so product claims (and hence permutation and lookup grand products) reduce to zero-checks and evaluations of $\widetilde{v}$ and $\widetilde{f}$, enabling linear-time provers.

## Proof sketch

The values $v(1,x)$ for $x\ne(1,\dots,1)$ encode the internal nodes of a binary product tree whose leaves are $v(0,x)=f(x)$; the recursion $v(1,x)=v(x,0)v(x,1)$ shifts indices so that each internal node is the product of its two children, and the node $(1,\dots,1,0)$ is the root. Conversely the identities force the root to equal the full product.

## Depends on

- [Multilinear extension of a Boolean function](../../../../TheoryOfComputation/hierarchy-theorems-and-barriers/algebrization-barrier/multilinear-ext.md)

## Proof depends on

- [Zero-check reduction to sum-check via the equality polynomial](zerocheck-reduction.md)

## Sources

- Binyi Chen, Benedikt Bünz, Dan Boneh, Zhenfei Zhang, "HyperPlonk: Plonk with Linear-Time Prover and High-Degree Custom Gates", EUROCRYPT (2023), IACR ePrint 2022/1355.
