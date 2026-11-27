# Non-negative Tucker decomposition of tissue modules

Let $\mathcal{X} \in \mathbb{R}_{\ge 0}^{P \times T \times M}$ be the tensor whose entry $\mathcal{X}_{p,t,m}$ is the frequency of cell type $t$ inside neighbourhood $m$ in sample $p$. A non-negative Tucker decomposition of multilinear rank $(r_1,r_2,r_3)$ is a choice of a core tensor $\mathcal{G} \in \mathbb{R}_{\ge 0}^{r_1 \times r_2 \times r_3}$ and factor matrices $A \in \mathbb{R}_{\ge 0}^{P \times r_1}$, $B \in \mathbb{R}_{\ge 0}^{T \times r_2}$, $C \in \mathbb{R}_{\ge 0}^{M \times r_3}$ minimizing

$$\big\lVert \mathcal{X} - \mathcal{G} \times_1 A \times_2 B \times_3 C \big\rVert_F^2, \qquad \big(\mathcal{G} \times_1 A \times_2 B \times_3 C\big)_{p,t,m} = \sum_{\alpha,\beta,\gamma} \mathcal{G}_{\alpha\beta\gamma}\, A_{p\alpha} B_{t\beta} C_{m\gamma},$$

where $\times_n$ is the mode-$n$ product and $\lVert \cdot \rVert_F$ the Frobenius norm. The columns of $B$ are cell-type modules, the columns of $C$ are neighbourhood modules, and the slice $\mathcal{G}_{\alpha,\cdot,\cdot}$ gives the coupling between the two kinds of module in the sample group indexed by $\alpha$.

## Depends on

- [Neighbourhood composition vector and cellular neighbourhoods](neighborhood-composition-vector-and-clustering.md)

## Remarks

Tucker generalizes the singular value decomposition to three modes: each mode gets its own basis, and the core tensor records how strongly every triple of basis elements interacts, so unlike a rank-one (CP) decomposition it can represent a cell-type module that participates in several neighbourhood modules with different weights. The non-negativity constraint makes factors additive parts rather than signed contrasts, which is what allows a column of $B$ to be read as a set of co-occurring cell types. The multilinear rank is not identified by the data alone and is chosen by inspecting the reconstruction loss as the ranks increase; the objective is non-convex, so stability across random initializations is the practical check on a reported decomposition.

## Sources

- Schurch CM, Bhate SS, Barlow GL, et al. Coordinated cellular neighborhoods orchestrate antitumoral immunity at the colorectal cancer invasive front. *Cell* 182:1341-1359 (2020), STAR Methods, "Non-negative Tucker tensor decomposition". DOI <https://doi.org/10.1016/j.cell.2020.07.005>. PMCID PMC7479520.
