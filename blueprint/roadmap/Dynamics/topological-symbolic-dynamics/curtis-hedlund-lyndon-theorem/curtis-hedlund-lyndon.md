# Curtis–Hedlund–Lyndon theorem

Let $A$ and $B$ be finite sets with the discrete
topology, and give $A^{\mathbb{Z}}$ and $B^{\mathbb{Z}}$ the product topology. For
$k \in \mathbb{Z}$ let $\sigma^k$ be the shift on either space given by
$(\sigma^k x)_n = x_{n+k}$ for all $n \in \mathbb{Z}$. A map
$F : A^{\mathbb{Z}} \to B^{\mathbb{Z}}$ is a sliding block code, that is, there are a radius
$r \in \mathbb{N}$ and a local rule $\varphi : A^{2r+1} \to B$ with
$F(x)_n = \varphi(x_{n-r}, \dots, x_{n+r})$ for all $x \in A^{\mathbb{Z}}$ and $n \in \mathbb{Z}$,
if and only if $F$ is continuous and commutes with every shift: $F(\sigma^k x) = \sigma^k F(x)$
for all $x \in A^{\mathbb{Z}}$ and $k \in \mathbb{Z}$.

## Sources

- https://en.wikipedia.org/wiki/Curtis%E2%80%93Hedlund%E2%80%93Lyndon_theorem (statement id `curtis-hedlund-s1`). Proves `Wanted` entry `curtis_hedlund_lyndon`.
