# Compatibility of trees with different leaf sets

**Setting.** Let $\mathbf T=\{T_1,\dots,T_k\}$ be binary metric phylogenetic trees with leaf sets $\mathcal L_r\subset[N]$, $|\mathcal L_r|=n_r$, $\bigcup_r\mathcal L_r=[N]$, and let $E_{T_r}^N\subset\mathcal T^N$ be their extension spaces in BHV tree space (all trees on $[N]$ whose restriction to $\mathcal L_r$ is $T_r$). The set $\mathbf T$ is **combinatorially compatible** if some tree topology on $[N]$ restricts to the topology of every $T_r$, and **compatible** if the intersection extension region $E_{\mathbf T}=\bigcap_rE_{T_r}^N$ is nonempty, that is, some metric tree on $[N]$ restricts exactly to every $T_r$.

**Results.**

1. *(Topological compatibility.)* A topology $C$ on $[N]$ lies in the common connection space if and only if $\Psi_{\mathcal L_r}(S(C))=S(T_r)$ for every $r$. Enumerating these topologies takes $O(2^{3\ell_1}n_1^4k^2)$ time, where $\ell_1=N-n_1$.
2. *(Intersection.)* In every orthant $\mathcal O$, $E_{\mathbf T}^{\mathcal O}=\bigcap_rE_{T_r}^{\mathcal O}$, and $E_{\mathbf T}^N=\bigcap_rE_{T_r}^N$; it is the solution set of the stacked system $M^{\mathcal O}_{\mathbf T}\mathbf x^{\mathcal O}=\mathbf w_{\mathbf T}$, $\mathbf x^{\mathcal O}\ge0$. Whether a given tree lies in $E_{\mathbf T}^N$ is decided in $O(kN)$ time.
3. *(Uniform relaxation.)* Replacing each equation $\sum_jx_j=w_i$ by $w_i-\alpha\le\sum_jx_j\le w_i+\alpha$ defines the $\alpha$-extension region $E_T^N(\alpha)$. If a tree lies in the relaxed region of $T$ in an orthant $\mathcal O$, its restriction is within distance $c\alpha$ of $T$, with $c$ depending only on $\mathcal O$ and $\mathcal L(T)$. If $\alpha<\log_2(N)^{-1}\min_{e}w_e$, then $E_T^N(\alpha)$ contains the $\alpha$-neighborhood of $E_T^N$. The regions increase with $\alpha$.
4. *(Intersection parameter as a linear program.)* The smallest $\alpha$ for which the relaxed intersection region in $\mathcal O$ is nonempty is the optimum of

$$
\min\ \alpha\quad\text{s.t.}\quad M^{\mathcal O}_{\mathbf T}\mathbf x^{\mathcal O}+\mathbf y_P-\mathbf y_N=\mathbf w_{\mathbf T},\qquad \mathbf x^{\mathcal O}\ge0,\qquad 0\le\mathbf y_P,\mathbf y_N\le\alpha,
$$

and the intersection parameter $\alpha_{\mathbf T}$ is the minimum over orthants. A proportional variant, with tolerances $p_\alpha w_i$, is again a linear program.

## Depends on

- [Extension space of a tree in BHV tree space](extension-space-of-a-tree-in-bhv-tree-space.md)

## Expansion

Each extension space is locally a codimension-$(2n_r-3)$ affine piece in every orthant, so two such pieces generically fail to meet once $n_r+n_{r'}>N+1$, and small estimation error in gene trees on overlapping taxon sets would make true supertree compatibility look like conflict. The relaxation replaces exact restriction by an $\ell_\infty$ tolerance on the induced edge lengths; because the relaxed regions are polytopes in each orthant, the minimum tolerance at which the trees become compatible is computed orthant by orthant by linear programming and serves as a quantitative measure of agreement between trees on different leaf sets.

## Sources

- Gillian Grindstaff and Megan Owen, "Geometric comparison of phylogenetic trees with different leaf sets", arXiv (2018), Section 4 (Proposition 4.2, Definition 4.3, Proposition 4.4, Definition 4.6, Proposition 4.7, Proposition 4.8) and Section 5 (Proposition 5.4, Proposition 5.5, Lemma 5.6, Definition 5.7, Proposition 5.8, Proposition 5.12), <https://doi.org/10.48550/arXiv.1807.04235> Published version: SIAM Journal on Applied Algebra and Geometry 3 (2019) 691–720, <https://doi.org/10.1137/18M1235855>.
