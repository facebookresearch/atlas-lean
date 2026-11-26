# Coagulation equations and branching representations for structured coalescents

**Model.** There are $d$ colonies (colours) with a primitive migration matrix $W=(w_{i,j})$ and coalescence rates $\alpha_i>0$. Sample $N_K$ individuals and trace lineages backward: each block (ancestral lineage, identified with its set of sampled descendants) moves from colony $i$ to $j$ at rate $Kw_{i,j}$, and each pair of blocks in colony $i$ merges at rate $\alpha_i$ (Kingman's coalescent within colonies). A block has *configuration* $\mathbf{k}\in\mathbb{N}_0^d$ if it carries $k_j$ sampled leaves from colony $j$. Let $\nu^K_i(t,\{\mathbf{k}\})$ count blocks in colony $i$ with configuration $\mathbf{k}$, let $\gamma_K=N_K/K$, $s_K=1$ if $\gamma_K\to c\in(0,\infty)$ (critical sampling) and $s_K=\gamma_K$ if $\gamma_K\to\infty$ (large sampling), and set

$$\mu^K_i(t,d\mathbf{x})=\tfrac1K\,\nu^K_i\big(\tfrac tK,s_K\,d\mathbf{x}\big).$$

Assume the initial fraction of blocks in colony $i$ converges: $L^K_i(0)/N_K\to\beta_i$.

**Statements.** Write $u\star u$ for the convolution in the configuration variable.
1. *(Critical sampling, $\gamma_K\to c$.)* $(\mu^K_i)_i$ converges weakly to the solution of the discrete coagulation-migration equation

$$\partial_tu_i(t,\mathbf{n})=\alpha_i\Big(\tfrac12u_i\star u_i(t,\mathbf{n})-\langle u_i(t),1\rangle u_i(t,\mathbf{n})\Big)+\sum_{j\neq i}\big(w_{j,i}u_j(t,\mathbf{n})-w_{i,j}u_i(t,\mathbf{n})\big),\quad u_i(0,\mathbf{n})=c\beta_i\,\delta_{\mathbf{e}_i,\mathbf{n}} .$$

2. *(Large sampling, $\gamma_K\to\infty$.)* $(\mu^K_i)_i$ converges to the weak solution of the same equation on $\mathbb{R}^d_+$, with the singular initial condition $\lim_{t\to0}\int(1-e^{-\langle\boldsymbol\lambda,\mathbf{x}\rangle})u_i(t,d\mathbf{x})=\lambda_i\beta_i$ for all $\boldsymbol\lambda>0$.
3. *(Feller representation.)* Any weak solution in case 2 equals $u_i(t,d\mathbf{x})=\beta_iQ_i(t,d\mathbf{x})$, where $Q_i$ is the entrance law from colour $i$ of the $d$-type Feller diffusion

$$dZ_i=\sqrt{\alpha_i\beta_iZ_i}\,dB_i+\sum_{j\neq i}\Big(w_{j,i}\tfrac{\beta_j}{\beta_i}Z_j-w_{i,j}Z_i\Big)dt ;$$

in particular the solution is unique.
4. *(Branching representation.)* In case 1, if $d_i:=\tfrac{c\alpha_i\beta_i}{2}-\sum_{j\neq i}\big(\tfrac{\beta_j}{\beta_i}w_{j,i}-w_{i,j}\big)>0$ for all $i$, any solution equals $u_i(t,\mathbf{n})=c\beta_i\,\mathbb{P}_{\mathbf{e}_i}(\mathbf{Z}(t)=\mathbf{n})$ for a continuous-time multi-type branching process in which a colour-$i$ particle branches at rate $c\alpha_i\beta_i/2$, dies at rate $d_i$ and changes from colour $i$ to colour $j$ at rate $\tfrac{\beta_j}{\beta_i}w_{j,i}$; the discrete equation has at most one solution.

## Depends on

- [Coalescing random walks dual to the voter and Moran models](../structured-coalescent/coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

On the time-scale $t/K$ with $O(K)$ blocks per colony, pairwise coalescence in colony $i$ removes blocks at total rate $\alpha_i\binom{K\langle u_i,1\rangle}{2}/K\approx\tfrac{\alpha_i}{2}K\langle u_i,1\rangle^2$, which after dividing by $K$ gives the quadratic Smoluchowski terms with constant kernel, while migration at rate $Kw_{i,j}$ per block gives the linear transport terms; generator convergence plus tightness of the measure-valued processes yields the limit. In the large sampling regime, blocks first coalesce down to order $K$ in a vanishing time, sizes being of order $\gamma_K$, which produces the singular initial condition. Taking Laplace transforms turns the coagulation equation into the Riccati system for the Laplace exponent of a continuous-state branching process, which identifies the solution through the Feller diffusion's entrance law; this is the forward-in-time branching picture dual to backward coalescence.

## Sources

- Fernando Cordero, Sophia-Marie Mellis, Emmanuel Schertzer, "Structured coalescents, coagulation equations and multi-type branching processes", arXiv:2505.09400 (2025), Section 2 (model, Assumption 1, Theorems 2.4, 2.5, 2.7 and 2.9), Proposition A.1, <https://doi.org/10.48550/arXiv.2505.09400>.
