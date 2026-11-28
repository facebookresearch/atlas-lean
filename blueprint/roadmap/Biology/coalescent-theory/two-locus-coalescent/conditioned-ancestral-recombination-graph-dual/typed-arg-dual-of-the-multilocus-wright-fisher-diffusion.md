# Typed ARG dual of the multilocus Wright–Fisher diffusion with recombination

**Forward model.** Haplotypes are $\mathbf i = (i_1,\dots,i_L) \in E = E_1 \times \dots \times E_L$ with finite allele sets $E_l$. Locus $l$ mutates at rate $\theta_l/2$ with transition matrix $P^{(l)}$ (having stationary law $\mu^{(l)}$), and recombination between loci $l$ and $l+1$ occurs at rate $\rho_l/2$. For nonempty $A \subseteq [L]$ write $E_A = \prod_{l\in A} E_l$, $x^A_{\mathbf i}$ for the marginal frequency of $\mathbf i \in E_A$, and $A_{\le l} = A \cap \{1,\dots,l\}$, $A_{>l} = A \cap \{l+1,\dots,L\}$. The Wright–Fisher diffusion $\mathbf X$ on the simplex $\Delta_E$ has generator

$$\mathcal L = \frac12 \sum_{\mathbf i \in E}\Big[\sum_{\mathbf j\in E} x_{\mathbf i}(\delta_{\mathbf i\mathbf j} - x_{\mathbf j})\partial_{x_{\mathbf j}} + \sum_{l=1}^L \theta_l\Big(\sum_{j \in E_l} P^{(l)}_{j i_l}\, x_{\mathbf i[l\to j]} - x_{\mathbf i}\Big) + \sum_{l=1}^{L-1}\rho_l\big(x^{[l]_{\le}}_{\mathbf i}\, x^{[l]_{>}}_{\mathbf i} - x_{\mathbf i}\big)\Big]\partial_{x_{\mathbf i}},$$

so the first term is the second-order operator $\frac12\sum_{\mathbf i,\mathbf j}x_{\mathbf i}(\delta_{\mathbf i\mathbf j}-x_{\mathbf j})\partial_{x_{\mathbf i}}\partial_{x_{\mathbf j}}$ of genetic drift and the other two are first-order drift terms. Here $\mathbf i[l\to j]$ replaces the $l$-th allele by $j$ and $x^{[l]_\le}_{\mathbf i}, x^{[l]_>}_{\mathbf i}$ are marginal frequencies of the left and right parts of $\mathbf i$.

**Dual state space.** A configuration $\mathbf n = (n^A_{\mathbf i})_{\emptyset\ne A\subseteq[L],\,\mathbf i\in E_A}$ of total size $n$ counts lineages that are ancestral to the sample exactly at the loci in $A$ and carry partial haplotype $\mathbf i$ there. Let

$$\widetilde m(\mathbf n) = \mathbb E\Big[\prod_{A}\prod_{\mathbf i \in E_A} (X^A_{\mathbf i})^{n^A_{\mathbf i}}\Big]$$

under the stationary law of $\mathbf X$, and let $\mathbf e^A_{\mathbf i}$ denote a unit vector.

**Theorem.** $\mathbf X$ is dual, with duality function $\widetilde F(\mathbf x,\mathbf n) = \widetilde Q(\mathbf x,\mathbf n)/\mathbb E[\widetilde Q(\mathbf X_\infty,\mathbf n)]$ where $\widetilde Q(\mathbf x,\mathbf n) = \binom{n}{\mathbf n}\prod_A\prod_{\mathbf i}(x^A_{\mathbf i})^{n^A_{\mathbf i}}$, to the pure-jump process $\widetilde{\mathbf L}$ with transitions

- **coalescence:** for nonempty $A,B$ and $\mathbf i \in E_{A\cup B}$, $\mathbf n \to \mathbf n - \mathbf e^A_{\mathbf i} - \mathbf e^B_{\mathbf i} + \mathbf e^{A\cup B}_{\mathbf i}$ at rate $\dfrac12 \dfrac{\widetilde m(\mathbf n - \mathbf e^A_{\mathbf i} - \mathbf e^B_{\mathbf i} + \mathbf e^{A\cup B}_{\mathbf i})}{\widetilde m(\mathbf n)}\, n^A_{\mathbf i}(n^B_{\mathbf i} - \delta_{AB})$;
- **mutation:** for $l \in A$, $\mathbf i \in E_A$, $j \in E_l$, $\mathbf n \to \mathbf n - \mathbf e^A_{\mathbf i} + \mathbf e^A_{\mathbf i[l\to j]}$ at rate $\dfrac12\dfrac{\widetilde m(\mathbf n - \mathbf e^A_{\mathbf i} + \mathbf e^A_{\mathbf i[l\to j]})}{\widetilde m(\mathbf n)}\, n^A_{\mathbf i}\,\theta_l P^{(l)}_{j i_l}$;
- **recombination:** for $\min A \le l < \max A$, $\mathbf n \to \mathbf n - \mathbf e^A_{\mathbf i} + \mathbf e^{A_{\le l}}_{\mathbf i} + \mathbf e^{A_{>l}}_{\mathbf i}$ at rate $\dfrac12\dfrac{\widetilde m(\mathbf n - \mathbf e^A_{\mathbf i} + \mathbf e^{A_{\le l}}_{\mathbf i} + \mathbf e^{A_{>l}}_{\mathbf i})}{\widetilde m(\mathbf n)}\, n^A_{\mathbf i}\,\rho_l$.

Consequently the transient sampling distributions satisfy

$$\mathbb E\big[\widetilde Q(\mathbf X_t,\mathbf n) \mid \mathbf X_0 = \mathbf x\big] = \mathbb E\Big[\frac{\mathbb E[\widetilde Q(\mathbf X_\infty,\mathbf n)]}{\mathbb E[\widetilde Q(\mathbf X_\infty,\widetilde{\mathbf L}_t)\mid \widetilde{\mathbf L}_t]}\,\widetilde Q(\mathbf x,\widetilde{\mathbf L}_t)\,\Big|\, \widetilde{\mathbf L}_0 = \mathbf n\Big].$$

Unlike the untyped ancestral recombination graph, lineages here are typed and the rates are ratios of stationary sampling probabilities, i.e. they describe the genealogy conditioned on the observed sample; lineages not ancestral to the sample at any locus are never created.

## Depends on

- [Coalescent with recombination: ancestral-material state space and generator](../coalescent-with-recombination-ancestral-material.md)
- [The neutral K-allele Wright–Fisher semigroup on the simplex by multinomial duality](../../../population-genetics/diffusion-theory/wright-fisher-semigroup-and-moment-duality/neutral-k-allele-semigroup-on-the-simplex-via-mu.md)

## Expansion

Duality $\mathbb E_{\mathbf x}[\widetilde F(\mathbf X_t,\mathbf n)] = \mathbb E_{\mathbf n}[\widetilde F(\mathbf x,\widetilde{\mathbf L}_t)]$ is verified at the level of generators: applying $\mathcal L$ to the monomial $\widetilde Q(\cdot,\mathbf n)$ gives a linear combination of $\widetilde Q(\cdot,\mathbf n')$ for neighbouring configurations $\mathbf n'$, with negative diagonal coefficient. Dividing by the stationary moments $\mathbb E[\widetilde Q(\mathbf X_\infty,\cdot)]$ turns that combination into a conservative rate matrix (the off-diagonal rates sum to the diagonal one precisely because stationary moments satisfy the corresponding recursion), so $\mathcal L \widetilde F(\cdot,\mathbf n)(\mathbf x) = \sum_{\mathbf n'} q(\mathbf n,\mathbf n')\,[\widetilde F(\mathbf x,\mathbf n') - \widetilde F(\mathbf x,\mathbf n)]$, which is the generator form of duality.

## Sources

- Robert C. Griffiths, Paul A. Jenkins and Sabin Lessard, *A coalescent dual process for a Wright–Fisher diffusion with recombination and its application to haplotype partitioning*, Theor. Popul. Biol. 112 (2016), 126–138. <https://doi.org/10.1016/j.tpb.2016.08.007> Equation (19) (generator), Section 3.2, the equations for $\widetilde Q$ and $\widetilde F$, Theorem 1 and Corollary 1. Corrigendum: Theor. Popul. Biol. 130 (2019), 203. <https://doi.org/10.1016/j.tpb.2019.08.001> Locators use the numbering of the preprint arXiv:1604.04145. Its latest version corrects typographical errors in equations (25)–(27), (B.3) and (B.4).
