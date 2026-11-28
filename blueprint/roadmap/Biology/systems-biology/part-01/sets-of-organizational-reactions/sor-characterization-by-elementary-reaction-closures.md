# SOR characterization by elementary reaction closures

**Reaction network.** Species $\mathcal{S} = \{s_1,\dots,s_n\}$ and reactions $\mathcal{R} = \{r_1,\dots,r_m\}$, $r_j : \sum_i a_{ij} s_i \to \sum_i b_{ij} s_i$ with $a_{ij}, b_{ij} \in \mathbb{N}$; the support of $r_j$ is $\operatorname{supp}(r_j) = \{s_i : a_{ij} > 0\}$ and the stoichiometric matrix is $N = (b_{ij} - a_{ij}) \in \mathbb{R}^{n \times m}$. Reversible reactions are split into two reactions.

**Closure, feasibility, organizations.** For $S \subseteq \mathcal{S}$ let $\operatorname{clos}_1(S) = S \cup \{s_i : \exists r_j,\ \operatorname{supp}(r_j) \subseteq S,\ b_{ij} > 0\}$, and let $\operatorname{clos}(S)$ be the limit of the increasing iteration of $\operatorname{clos}_1$ (reached after finitely many steps). A flux $v \in \mathbb{R}^m_{+}$ is **feasible** for $S$ if $v_r > 0 \iff \operatorname{supp}(r) \subseteq S$ for every $r$. $S$ is **closed** if $\operatorname{clos}(S) = S$, **self-maintaining** if some feasible $v$ has $Nv \ge 0$, and an **organization** if both.

**Distributed organization (DO).** $D \subseteq \mathcal{S}$ is a DO through $\hat v \in \mathbb{R}^m_+$ if $D = S_1 \cup \dots \cup S_k$ for pairwise different closed sets $S_i$ (compartments), $N\hat v \ge 0$, and $\hat v = \sum_i \hat v^i$ with each $\hat v^i$ feasible for $S_i$. A DO with $k = 1$ is an organization.

**SOR.** If $D$ is a DO through a flux $\hat v$, in the compartment-wise sense above (each $\hat v^i$ feasible for its own closed $S_i$, with no feasibility of $\hat v$ for $D$ itself), then $\mathrm{SOR}(\hat v) = \{r_j : \hat v_j > 0\}$ is a **set of organizational reactions**. The source's Definition 6 prints "a feasible flux $\hat v$ with respect to $D$"; the page drops that condition because with it Lemma 3 below is false: for $r_1 : a \to 2a$, $r_2 : b \to 2b$, $r_3 : a + b \to c$ and $\hat v = (1,1,0)$, $N\hat v \ge 0$ and $R = \{r_1,r_2\} = \mathrm{ERC}(r_1) \cup \mathrm{ERC}(r_2)$, yet any flux feasible for a DO containing $a$ and $b$ has $\hat v_3 > 0$. A species $s_i$ is overproduced by $\hat v$ if $(N\hat v)_i > 0$.

**Elementary reaction closure (ERC).** For $\hat r \in \mathcal{R}$,

$$\mathrm{ERC}(\hat r) = \{ r \in \mathcal{R} : \operatorname{supp}(r) \subseteq \operatorname{clos}(\operatorname{supp}(\hat r)) \},$$

the reactions switched on once $\hat r$ runs.

**Lemma 3 (equivalent definition).** $R \subseteq \mathcal{R}$ is a SOR iff there is $\hat v \in \mathbb{R}^m_+$ with

1. self-maintenance: $N\hat v \ge 0$, and
2. closedness with full support: $R = \{r_j : \hat v_j > 0\} = \bigcup\{\mathrm{ERC}(r_j) : \hat v_j > 0\}$.

**Lemma 1.** Each SOR has a unique largest set of species that some flux supported exactly on it overproduces.

**Lemma 2.** The SORs of a reaction network form a lattice.

## Expansion

For Lemma 3, given such $\hat v$ with $R = \{r_1,\dots,r_k\}$, so that $\hat v_j > 0$ exactly for $r_j \in R$, take compartments $S_i = \operatorname{clos}(\operatorname{supp}(r_i))$, which are closed and support exactly $\mathrm{ERC}(r_i)$. Split each reaction's rate evenly over the compartments that support it: with $l(j)$ the number of $S_i \supseteq \operatorname{supp}(r_j)$, set $\hat v^i_j = \hat v_j / l(j)$ if $\operatorname{supp}(r_j) \subseteq S_i$ and $0$ otherwise. Each $\hat v^i$ is feasible for $S_i$, they sum to $\hat v$, and $\bigcup_i S_i$ is a DO through $\hat v$ whose SOR is $R$. The converse reads the two properties off the definition of a DO. The source states Lemma 3 with closedness alone, $R = \bigcup\{\mathrm{ERC}(r_j) : \hat v_j > 0\}$, which is too weak: for $r_1 : a \to b$, $r_2 : b \to a$, $r_3 : a \to \emptyset$, every ERC is $\{r_1,r_2,r_3\}$ and $\hat v = (1,1,0)$ has $N\hat v = 0$, yet no flux positive on all three reactions has $Nv \ge 0$ (row $b$ needs $v_1 \ge v_2$, row $a$ needs $v_2 \ge v_1 + v_3$), so $\{r_1,r_2,r_3\}$ is not a SOR. The even split above needs $\hat v_j > 0$ on every reaction of each $\mathrm{ERC}(r_i)$. Lemma 1 takes the union of the overproduced sets over all fluxes with the same support.

The characterization is what makes enumeration practical: closedness becomes a union of precomputed ERCs, and self-maintenance is a linear feasibility problem. A maximal compartment of a DO–SOR pair is a closed species set supporting no reaction outside the SOR; minimal compartmentalizations are selected among maximal compartments.

## Sources

- S. Peter, L. Woitke, P. Dittrich, B. Ibrahim, "Computing all persistent subspaces of a reaction-diffusion system", Scientific Reports 13 (2023) 17169, Definitions 1–7 and Lemmas 1–3, <https://doi.org/10.1038/s41598-023-44244-x>, PMCID PMC10567720.
