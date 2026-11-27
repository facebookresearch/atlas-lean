# Identifiability of batch effects under connected designs

**Setting.** The negative-binomial mixture model with expression-dependent dropout (parameters $\Theta = \{\alpha,\beta,\nu,\phi,\Delta,\Gamma,\pi\}$) on $B$ batches and $K$ cell types. Let $C_b = \{k : \pi_{bk} > 0\}$ be the cell types present in batch $b$, with $\bigcup_b C_b = \{1,\dots,K\}$. Assume
- (I) $\gamma_{b1} < 0$ for every batch (dropout decreases with expression);
- (II) every pair of cell types $k_1 \ne k_2$ has at least two differentially expressed genes $g_1, g_2$: $\beta_{g_1k_1} \ne \beta_{g_1k_2}$ and $\beta_{g_2k_1}\ne\beta_{g_2k_2}$;
- (III) ordered pairs of distinct cell types, $k_1 \ne k_2$ and $k_3 \ne k_4$, with $(k_1,k_2) \ne (k_3,k_4)$ have distinct effect differences, $\beta_{\cdot k_1} - \beta_{\cdot k_2} \ne \beta_{\cdot k_3} - \beta_{\cdot k_4}$.

**Identifiability** means: $L_o(\Theta \mid y) = L_o(\Theta^* \mid y)$ for all $y$ implies, for a permutation $\rho$ of cell-type labels, $\pi_{bk} = \pi^*_{b\rho(k)}$, $(\gamma_{b0},\gamma_{b1}) = (\gamma^*_{b0},\gamma^*_{b1})$, $\alpha_g + \beta_{gk} = \alpha^*_g + \beta^*_{g\rho(k)}$, $\nu_{bg} = \nu^*_{bg}$, $\delta_{bi} = \delta^*_{bi}$ and $\phi_{bg} = \phi^*_{bg}$.

**Theorem.** Under (I)–(III) the model is identifiable (up to label switching) in each of the following designs:
1. *complete:* $\pi_{bk} > 0$ for all $b, k$;
2. *reference panel:* some batch contains all $K$ cell types and every batch has $|C_b| \ge 2$;
3. *chain:* consecutive batches share at least two cell types, $|C_b \cap C_{b-1}| \ge 2$ for $b \ge 2$;
4. *connected (general):* the batch graph, with an edge between two batches iff they share at least two cell types, is connected.

A completely confounded design (each batch containing a single, batch-specific cell type) is not identifiable by any method.

## Depends on

- [Negative-binomial mixture model with expression-dependent dropout](negative-binomial-mixture-model-with-expression-dependent-dropout.md)

## Expansion

Within one batch, a generating-function-type argument recovers the mixture components and the dropout curve up to relabelling; condition (I) separates dropout zeros from biological zeros. Two shared cell types in two batches give the same difference $\beta_{k_1} - \beta_{k_2}$ in both, and condition (III) makes this difference a fingerprint that matches components across batches, after which the shift between matched components identifies $\nu_{bg}$. Connectivity of the batch graph propagates the alignment from the reference batch to every batch, which contains designs 1–3 as special cases and permits studies in which no batch assays all cell types.

## Sources

- F. Song, G. M. A. Chan, Y. Wei, "Flexible experimental designs for valid single-cell RNA-sequencing experiments allowing batch effects correction", Nature Communications 11 (2020) 3274, Methods (experimental designs), Theorems 1–4 and Supplementary Note 3, <https://doi.org/10.1038/s41467-020-16905-2>, PMCID PMC7330047.
