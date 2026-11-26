# Error polynomial when folding relaxed degree-d verifier checks

Let $\Phi(\mu,\pi)=\sum_{j=0}^{d}\mu^{d-j}V_j(\pi)$ for a homogeneous decomposition of a degree-$d$ map, where $\pi$ collects all transcript elements. For an accumulator $(\mu,\pi)$ with error $\mathbf{e}=\Phi(\mu,\pi)$ and a fresh transcript $(1,\pi')$ with $\Phi(1,\pi')=\mathbf{0}$, the map $X\mapsto\Phi(\mu+X,\pi+X\pi')$ is a vector of polynomials of degree at most $d$ in $X$,

$$
\Phi(\mu+X,\pi+X\pi')=\mathbf{e}+\sum_{i=1}^{d-1}\mathbf{e}_iX^{i}+\mathbf{0}\cdot X^{d},
$$

since its constant coefficient is $\Phi(\mu,\pi)=\mathbf{e}$ and its leading coefficient is $\Phi(1,\pi')=\mathbf{0}$ by homogeneity. After the prover commits to $\mathbf{e}_1,\dots,\mathbf{e}_{d-1}$ and the verifier picks random $\alpha$, the folded accumulator $(\mu+\alpha,\pi+\alpha\pi')$ has error $\mathbf{e}+\sum_i\alpha^{i}\mathbf{e}_i$.

## Proof sketch

Each $V_j$ is homogeneous of degree $j$, so $(\mu+X)^{d-j}V_j(\pi+X\pi')$ is a polynomial of degree at most $d$ in $X$ whose $X^{d}$ coefficient is $V_j(\pi')$ (taking $\mu$-part $1$). Summing over $j$ gives leading coefficient $\Phi(1,\pi')$ and constant coefficient $\Phi(\mu,\pi)$.

## Depends on

- [Special-sound protocols with algebraic degree-d verifiers](special-sound-algebraic-verifier.md)

## Sources

- Benedikt Bünz, Binyi Chen, "Protostar: Generic Efficient Accumulation/Folding for Special-Sound Protocols", ASIACRYPT (2023), IACR ePrint 2023/620.
