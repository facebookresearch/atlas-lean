# Galerkin projection of an agent-based adoption model onto a stochastic metapopulation model

**Agent-based model.** $n_a$ agents move in a domain $\mathbb X \subseteq \mathbb R^d$ and carry statuses in $\{1,\dots,n_s\}$. An agent in status $i$ moves as a diffusion with generator $\mathcal L_i$ (for example $dx = -\tfrac{\sigma^2}{2}\nabla U(x)\,dt + \sigma\,dB_t$). Status changes $i \to j$ occur either by *first-order* adoption at rate $\gamma_{ij}(x_\alpha)$, or by *second-order* adoption at rate $\sum_{\beta \ne \alpha} c_{ij}\, d_r(x_\alpha, x_\beta)\,\mathbf 1[s_\beta = j]$, where $d_r(x,y) = \mathbf 1[|x-y| \le r]$. The joint law $p(X,S,t)$ solves $\partial_t p = \mathcal L p + \mathcal G p$, with $\mathcal L$ the sum of the single-agent motion generators and $\mathcal G$ the jump generator of status adoptions.

**Projection.** Let $\mathbb X = A_1 \sqcup \dots \sqcup A_m$ be a partition into metastable sets. For a count matrix $N = (N_i^{(k)})$ with $\sum_{i,k} N_i^{(k)} = n_a$ let $\Phi_N(X,S)$ be the indicator that exactly $N_i^{(k)}$ agents lie in $A_k$ with status $i$. The functions $\Phi_N$ are orthogonal and form a partition of unity, and $Qv = \sum_N \frac{\langle \Phi_N, v\rangle}{\langle \Phi_N, 1\rangle}\Phi_N$ is the orthogonal projection onto their span. Define the coarse rates

$$\lambda_i^{(kl)} = \frac{\langle \mathbf 1_{A_l}, \mathcal L_i \mathbf 1_{A_k}\rangle}{\langle \mathbf 1_{A_k}, 1\rangle}, \qquad \gamma_{ij}^{(k)} = \frac{\int_{A_k}\gamma_{ij}}{|A_k|}, \qquad b_{kl} = \frac{\int_{A_k \times A_l} d_r(x_1,x_2)\,dx_1\,dx_2}{|A_k|\,|A_l|}.$$

Write $E_i^{(k)}$ for the unit count matrix with a one at $(i,k)$.

**Theorem.** The projected generators $Q\mathcal L Q$ and $Q\mathcal G Q$ have the following matrix representations on count states (off-diagonal entries; diagonals make rows sum to zero).
1. (Migration) $\hat L_{N, N - E_i^{(k)} + E_i^{(l)}} = \lambda_i^{(kl)} N_i^{(k)}$ for $k \ne l$.
2. (First-order adoption) $\hat G_{N, N - E_i^{(k)} + E_j^{(k)}} = \gamma_{ij}^{(k)} N_i^{(k)}$ for $i \ne j$.
3. (Second-order adoption) $\hat G_{N, N - E_i^{(k)} + E_j^{(k)}} = c_{ij} b_{kk} N_i^{(k)} N_j^{(k)} + \epsilon_{ij}^{(k)}(N)$, where $\epsilon_{ij}^{(k)}(N) = c_{ij}\sum_{l \ne k} b_{kl} N_i^{(k)} N_j^{(l)}$ collects cross-region contacts.

Dropping $\epsilon_{ij}^{(k)}$ yields the **stochastic metapopulation model**: a continuous-time Markov chain on count matrices with linear migration and mass-action within-region reactions, whose master equation is

$$\frac{dP(N,t)}{dt} = \sum_{k \ne l}\sum_i \lambda_i^{(kl)}\big[(N_i^{(k)}+1)P(N + E_i^{(k)} - E_i^{(l)}, t) - N_i^{(k)}P(N,t)\big] + \sum_{k}\sum_{i,j}\big[\hat f_{ij}^{(k)}(N')P(N',t) - \hat f_{ij}^{(k)}(N)P(N,t)\big],$$

with $N' = N + E_i^{(k)} - E_j^{(k)}$ and $\hat f_{ij}^{(k)}$ the within-region rates from items 2–3.

## Expansion

Because the ansatz functions are indicators of disjoint events, the matrix entries of $Q H Q$ are averages of the agent-level rates over the event $\{\Phi_N = 1\}$ under the uniform reference measure. For migration, only one agent moves at a time, and the averaged flux of $\mathcal L_i$ from $A_k$ into $A_l$ factorizes into the single-agent rate $\lambda_i^{(kl)}$ times the $N_i^{(k)}$ agents eligible to make the move. For second-order adoption, each pair of agents in regions $k, l$ is in contact with conditional probability $b_{kl}$, giving the bilinear terms. When the regions are metastable and the contact radius $r$ is small compared with the regions, mass near region boundaries is rare and $b_{kl} \ll b_{kk}$ for $k \ne l$, so $\epsilon_{ij}^{(k)}$ is negligible; in a double-well example it is orders of magnitude below the projection error. A further large-population limit of the metapopulation chain gives region-wise ODEs (a reaction-rate or mean-field model), so the projection sits between individual-based simulation and deterministic compartmental models.

## Sources

- S. Winkelmann, J. Zonker, C. Schütte, N. Djurdjevac Conrad, "Mathematical modeling of spatio-temporal population dynamics and application to epidemic spreading", Mathematical Biosciences 336 (2021) 108619, Eqs. (1)–(20), Theorems 1–3 and Example 1, <https://doi.org/10.1016/j.mbs.2021.108619>, PMCID PMC8054535.
