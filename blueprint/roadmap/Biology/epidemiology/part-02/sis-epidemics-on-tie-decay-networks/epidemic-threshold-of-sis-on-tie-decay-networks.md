# Epidemic threshold of the SIS process on tie-decay networks

Let $\mathbf B^{(\tau)}$, $\tau=0,1,\dots$, be the discretized snapshots of a tie-decay network on $N$ nodes. Run a discrete-time SIS process in which, during step $\tau$, an infected node $j$ infects a susceptible node $i$ with probability $\lambda_{ij}^{(\tau)}=\lambda_{\max}\min\{b_{ij}^{(\tau)},1\}$, independently over infected neighbours, and each infected node recovers with probability $\mu$. Under the assumption that neighbours' states are uncorrelated, the infection probabilities $p_i^{(\tau)}$ evolve by

$$p_i^{(\tau+1)}=1-\mu p_i^{(\tau)}-\bigl(1-p_i^{(\tau)}\bigr)\prod_{j=1}^N\Bigl(1-\lambda_{\max}\min\{b_{ij}^{(\tau)},1\}\,p_j^{(\tau)}\Bigr).$$

Assume the snapshots are periodic, $\mathbf B^{(\tau+l)}=\mathbf B^{(\tau)}$ for some period $l$ (which may be taken as large as the observation horizon). Define the one-step matrices and the **system matrix**

$$\mathbf S_\tau=(1-\mu)\mathbf I+\lambda_{\max}\min\{\mathbf B^{(\tau)},1\},\qquad \mathbf S=\prod_{\tau=0}^{l-1}\mathbf S_\tau ,$$

with $\min$ taken entrywise.

**Threshold.** If the spectral radius satisfies $\rho(\mathbf S)<1$, the disease-free state $\mathbf p=0$ is asymptotically stable, so the infection dies out from small initial prevalence. The epidemic threshold is $\rho(\mathbf S)=1$. Equivalently, in the supra-adjacency (multilayer) representation $\mathbf M\in\mathbb R^{Nl\times Nl}$ with blocks $\mathbf M^{\tau\tau'}=\delta_{\tau,\tau'-1}\mathbf S_\tau$, the threshold reads $\rho(\mathbf M)=\rho(\mathbf S)^{1/l}=1$.

The condition $\rho(\mathbf S_\tau)<1$ for every $\tau$ is sufficient but much more conservative: the infection can die out even if some snapshots are individually supercritical, because only the spectrum of the product matters.

## Expansion

Write the update as $\mathbf p_{\tau+1}=g_\tau(\mathbf p_\tau)$. At $\mathbf p=0$ the Jacobian of $g_\tau$ is $\mathbf S_\tau$ (expand the product to first order). Periodicity makes the one-period map $g_{l-1}\circ\dots\circ g_0$ autonomous, and by the chain rule its Jacobian at $0$ is $\mathbf S_{l-1}\cdots\mathbf S_0$, which has the same spectrum as $\mathbf S$. Linearized stability of a fixed point of a discrete map (dominant eigenvalue of modulus below $1$) then gives the threshold; cyclic permutations of the product have the same spectral radius, so stability does not depend on the phase within the period. In the multilayer formulation, $\mathbf M^l$ is block diagonal with cyclic products of the $\mathbf S_\tau$ on the diagonal, which gives $\rho(\mathbf M)^l=\rho(\mathbf S)$.

## Depends on

- [Tie-decay network](tie-decay-network.md)

## Sources

- Q. Chen and M. A. Porter, *Epidemic thresholds of infectious diseases on tie-decay networks*, arXiv:2009.12932 (2020), Section 3.1 (Derivation using a Nonlinear Dynamical System, lemma on the system matrix) and Section 3.2 (Derivation using a Multilayer Representation). <https://doi.org/10.48550/arXiv.2009.12932>
