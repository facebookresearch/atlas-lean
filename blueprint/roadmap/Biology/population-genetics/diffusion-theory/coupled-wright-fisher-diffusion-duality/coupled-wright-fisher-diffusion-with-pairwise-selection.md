# Coupled Wright–Fisher diffusion with pairwise selection

**Setting.** There are $L\ge1$ loci, and locus $l$ has $M_l$ alleles; set $M=\sum_lM_l$. Write $x=(x^{(1)},\dots,x^{(L)})$ with $x^{(l)}\in[0,1]^{M_l}$, and let the state space be

$$S=\Bigl\{x\in[0,1]^M:\ \textstyle\sum_{i=1}^{M_l}x^{(l)}_i=1\ \ \forall l\Bigr\}.$$

Selection is encoded by $V(x)=x^{\mathsf T}h+\tfrac12x^{\mathsf T}Jx$, where $h\in\mathbb R_+^M$ gives single-locus selection and $J\in\mathbb R_+^{M\times M}$ is symmetric with zero diagonal blocks $J^{(ll)}=0$, giving pairwise interactions between loci. The fitness of haplotype $\sigma=(i_1,\dots,i_L)$ is

$$w_\sigma=1+\sum_lh^{(l)}_{i_l}+\sum_{l<r}J^{(rl)}_{i_li_r}.$$

Mutation at locus $l$ goes from $i$ to $j$ at rate $u^{(l)}_{ij}=\tfrac{\theta_l}2P^{(l)}_{ij}$, independently across loci.

**Definition.** The coupled Wright–Fisher diffusion is the diffusion on $S$ with generator, on $C^2(S)$,

$$\mathcal Lf(x)=\sum_{l=1}^L\Bigl[\sum_{i=1}^{M_l}\bigl(\mu^{(l)}_i(x^{(l)})+g^{(l)}_i(x)\bigr)\partial_{x^{(l)}_i}f+\tfrac12\sum_{i,j=1}^{M_l}d^{(l)}_{ij}(x^{(l)})\,\partial^2_{x^{(l)}_ix^{(l)}_j}f\Bigr],$$

with mutation drift $\mu^{(l)}_i=\sum_j\bigl[u^{(l)}_{ji}x^{(l)}_j-u^{(l)}_{ij}x^{(l)}_i\bigr]$, Wright–Fisher covariance $d^{(l)}_{ij}=x^{(l)}_i(\delta_{ij}-x^{(l)}_j)$, and selection drift $g=D(x)\nabla V(x)$, that is $g^{(l)}_i=\sum_kd^{(l)}_{ik}\tilde h^{(l)}_k$ with $\tilde h^{(l)}_k=h^{(l)}_k+\sum_{r\ne l}\sum_mJ^{(lr)}_{km}x^{(r)}_m$.

**Proposition (stationary density).** Under parent-independent mutation, $u^{(l)}_{ij}=u^{(l)}_j$, the stationary density on the reduced coordinates $\bar x$ (dropping the last allele at each locus, whose frequency is one minus the others) is

$$p(\bar x)=\frac1Z\,\pi(\bar x)\,e^{2V(\bar x)},\qquad \pi(\bar x)=\prod_{l=1}^L\ \prod_{i=1}^{M_l}\bigl(x^{(l)}_i\bigr)^{2u^{(l)}_i-1},$$

a product of Dirichlet densities tilted by the exponential of the selection potential. For one biallelic locus,

$$Z=e^{2h_2}\,B(2u_1,2u_2)\,{}_1F_1\bigl(2u_1;\,2u_1+2u_2;\,2(h_1-h_2)\bigr).$$

## Depends on

- [Backward generator of the Wright–Fisher diffusion with selection](../wright-fisher-diffusion/generator.md)
- [Dirichlet distribution](../../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/dirichlet-measure.md)

## Proof depends on

- [The Dirichlet law is stationary for parent-independent mutation](../wright-fisher-diffusion-with-selection-and-mutat/dirichlet-stationary-law-for-parent-independent.md)

## Expansion

When $J=0$ the loci decouple into independent multi-allele Wright–Fisher diffusions, whose stationary laws under parent-independent mutation are Dirichlet (Wright's formula). With interactions, the covariance defines a Svirezhev–Shahshahani metric on the product of simplices, and the selection drift is the gradient of $V$ in this metric. This yields the explicit exponential tilt $e^{2V}$, with only the normalizing constant $Z$ left implicit. In the one-locus biallelic case, $Z$ reduces to a Kummer confluent hypergeometric function through its integral representation.

## Sources

- M. Favero, H. Hult, T. Koski, "A dual process for the coupled Wright–Fisher diffusion", *Journal of Mathematical Biology* 82(1):6 (2021), Section 1 (Eq. 2), Section 2 (Eqs. 5–10), Section 4 (one-locus normalizing constant), <https://doi.org/10.1007/s00285-021-01555-9>, PMCID PMC7822808.
