# Gene-expression deconvolution

Write the bulk matrix (genes × samples) as $C P$, the cell-type profiles $C \in \mathbb{R}^{m \times k}$
(with $k$ finite) times the cell-type proportions $P \in \mathbb{R}^{k \times n}$. If the
proportions $P_{aj}$ of sample $j$ are nonnegative and sum to $1$ and every cell type $a$
expresses gene $g$ at a level $C_{ga} \in [\mathit{lo}, \mathit{hi}]$, then the bulk level
$(C P)_{gj}$ of $g$ in sample $j$ lies in $[\mathit{lo}, \mathit{hi}]$.
