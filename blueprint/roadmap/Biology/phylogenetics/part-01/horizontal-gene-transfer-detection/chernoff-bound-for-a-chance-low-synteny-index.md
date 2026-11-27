# Chernoff bound for a chance-low synteny index

**Definitions.** A genome is an ordered set of genes. The $k$-neighbourhood $N_k(G,g_0)$ of gene $g_0$ in genome $G$ is the set of genes at most $k$ positions upstream or downstream of $g_0$ (excluding $g_0$). For genomes $G_1, G_2$, the **$k$-synteny index** of a common gene $g_0 \in G_1 \cap G_2$ is

$$\mathrm{SI}(g_0,G_1,G_2) = |N_k(G_1,g_0) \cap N_k(G_2,g_0)|,$$

and $\mathrm{SI} = 0$ for genes not in the core set. Genes in the symmetric difference $G_1 \triangle G_2$ are **singular**.

**Lemma.** Let $|G_1| = |G_2| = n$, $g \in G_1 \cap G_2$, $k \ll n$, and let neighbours be singular independently with probability $p = |G_1\triangle G_2|/(2n)$. For any $\delta_{\mathrm{SI}} \in (0,1)$,

$$\Pr\Big(\mathrm{SI} < \frac{k}{n}\big(2n - |G_1\triangle G_2|\big) - \sqrt{-k\log_e\delta_{\mathrm{SI}}}\Big) \le \delta_{\mathrm{SI}},$$

i.e. a synteny index below $2k(1-p) - \sqrt{-k\log\delta_{\mathrm{SI}}}$ arises from gene gain and loss alone with probability at most $\delta_{\mathrm{SI}}$, and the significance grows exponentially as $\mathrm{SI}$ decreases.

**Corollary (neighbourhood size).** A significant low synteny index can be certified at level $\delta_{\mathrm{SI}}$ only if

$$k \ge -\frac{\log_e \delta_{\mathrm{SI}}}{4(1-p)^2}.$$

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Expansion

Since both genomes have $n$ genes, half of the symmetric difference lies in each, so a random gene is singular with probability $p$. Centring the $2k$ neighbour indicators, $X = \sum_{i=1}^{2k}(\mathbf 1[g_i \text{ singular}] - p)$ equals $2k - \mathrm{SI} - 2kp$, and Hoeffding's (Chernoff) bound $\Pr(X > a) \le e^{-2a^2/(2k)}$ with $a = \sqrt{-k\log\delta_{\mathrm{SI}}}$ gives the lemma. Requiring the threshold to be non-negative gives the corollary: e.g. with $n = 1000$, $|G_1\triangle G_2| = 1600$ and $\delta_{\mathrm{SI}} = 0.05$, a window of $k = 10$ is too small but $k = 30$ suffices. A translocated or duplicated gene also has expected synteny index near $0$, so low synteny alone cannot distinguish transfer from rearrangement.

## Sources

- G. Sevillya, O. Adato, S. Snir, "Detecting horizontal gene transfer: a probabilistic approach", BMC Genomics 21(Suppl 1) (2020) 106, Definitions and methods, Lemma 1 (Eqs (1)–(5)), Corollaries 1–2 (Eq (6)) and Observation 2, <https://doi.org/10.1186/s12864-019-6395-5>, PMCID PMC7057450.
