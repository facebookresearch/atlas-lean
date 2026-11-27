# NP-hardness of the subtype-specific pathway linear progression problem

**Problem (SPM).** Input: an $m \times n$ matrix $C$ of cancer cell fractions, $C_{i,j}$ being the fraction of cancer cells of sample $i$ carrying a mutation in gene $j$; integers $K$ (pathways) and $T$ (subtypes); a tolerance $\epsilon \ge 0$. Output: a partition of the genes into $K$ pathways, a partition of the samples into $T$ subtypes, and for each subtype a linear order of the $K$ pathways, chosen to minimize the total cancer cell fraction of mutations declared false positives. Within a sample, each pathway is represented by one mutation (mutual exclusivity); its value $Z_{i,x}$ must be consistent with the subtype's order, in that pathway $x$ precedes $y$ in sample $i$ when $Z_{i,x} - Z_{i,y} > \epsilon$, while values within $\epsilon$ are ambiguous. The rationale is linear progression with irreversible mutations: earlier mutations have larger cancer cell fractions.

**Theorem.** The SPM problem is NP-hard for every $K \ge 2$, $T \ge 1$ and $\epsilon \ge 0$.

## Proof depends on

- [MAXIMUM CUT is NP-complete](../../../../TheoryOfComputation/np-completeness/graph-coloring-and-partitioning/maximum-cut/max-cut-np-complete.md)

## Expansion

The reduction is from weighted Minimum-UnCut: given $G = (V, E)$ with weights $w_e > 0$, split $V$ into $S, \bar S$ minimizing the weight of edges inside the parts. Use one gene per vertex plus $K - 1$ auxiliary genes, fix each subtype's order with pathways $K$ and $K-1$ in the first two positions, and for each edge $e = (u,v)$ and subtype create two samples in which $g_u = g_v = w_e + \Delta$ ($\Delta > \epsilon$) and the auxiliary genes take staggered large values $\hat w + \mathrm{Pos}_t(l)\Delta$ that pin the other pathways. Checking the four placements of $u, v$ shows that each edge costs $4w_e$, $3w_e$, $3w_e$ or $w_e$ over its two samples, the last exactly when $u$ and $v$ fall in different pathways among $K - 1$ and $K$. Hence an optimal solution places all vertex genes in pathways $K-1$ and $K$, its cost is $TW + 2\lambda_3$ with $W = \sum_e w_e$ and $\lambda_3$ the uncut weight, and it solves the Minimum-UnCut instance; the construction has $2T|E|$ rows and is polynomial. In practice the problem is solved exactly by an integer linear program.

## Sources

- S. Khakabimamaghani, D. Ding, O. Snow, M. Ester, "Uncovering the subtype-specific temporal order of cancer pathway dysregulation", PLoS Computational Biology 15(11) (2019) e1007451, Problem definition and Theorem 1 with its proof, <https://doi.org/10.1371/journal.pcbi.1007451>, PMCID: PMC6872169.
