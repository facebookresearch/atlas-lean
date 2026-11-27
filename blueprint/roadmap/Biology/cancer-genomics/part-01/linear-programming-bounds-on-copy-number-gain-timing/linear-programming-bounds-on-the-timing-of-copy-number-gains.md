# Linear-programming bounds on the timing of copy-number gains

Consider a clonal somatic copy-number gain region with total copy number $N_t$ and minor copy number $N_b$, reached from the diploid state by $K$ successive gain events (deletions ignored). The somatic timeline from the zygote to the tumour founder cell is split into stages $k=0,\dots,K$; let $t=(t_0,\dots,t_K)$ be the fractions of time spent in each stage, so $t\ge0$ and $\mathbf 1\cdot t=1$. Here $t_0$ is the initiation time (before the first gain) and $t_K$ the lead time (after the last gain). Let $a_j$ be the possible allele states of a clonal point mutation in the region (fractions $j/N_t$ of the allelic copies carrying it), and for a gain history let the history matrix $A$ have entry $A_{jk}$ equal to the number of copies present in stage $k$ whose mutations end in allele state $a_j$; its column sums $s_k$ are the copy numbers of the stages. Assume point mutations occur at a constant rate per copy. Then the probability $q_j$ that a randomly acquired clonal mutation has allele state $a_j$ satisfies

$$q=\frac{At}{s^{\mathsf T}t}\quad\Longleftrightarrow\quad (A-q\,s^{\mathsf T})\,t=0,\qquad \mathbf 1\cdot t=1 .$$

- If $A$ is square and invertible (for example single or double gains such as $3{:}1$, $2{:}0$, $4{:}1$, $3{:}0$), the timing is identified: $t=c\,A^{-1}q$ with $c=s^{\mathsf T}t$ fixed by $\mathbf 1\cdot t=1$.
- If $A$ is singular or the history is not unique (for example $5{:}1$ reached by three gains along different orderings), $t$ is not identified, but for each candidate history $A$ the linear programs

    $$\max_t\ t_K\quad\text{or}\quad\max_t\ t_0\qquad\text{s.t.}\quad (A-q\,s^{\mathsf T})\,t=0,\ \ \mathbf 1\cdot t=1,\ \ t\ge0$$

    give upper bounds on the lead time and on the initiation time; maximising over all histories compatible with $(N_t,N_b)$ bounds them over histories.

The vector $q$ is estimated from read counts by EM: for $M$ clonal mutations with $m_i$ mutant reads out of depth $d_i$, the log-likelihood conditioned on detection is

$$\sum_{i=1}^{M}\log\frac{\sum_j \Pr(m_i\mid f_i=a_j)\,q_j}{1-\sum_j(1-a_j)^{d_i}\,q_j},$$

with purity-adjusted allele frequency $f_i$ and binomial read sampling. Noise in $\hat q$ is absorbed by slack variables on the equality constraints, and confidence intervals come from bootstrapping the mutations.

## Expansion

A mutation acquired in stage $k$ lands on one of the $s_k$ copies present, and the number of copies it ends up on in the founder is fixed by which copies are later duplicated; the probability of acquiring it in stage $k$ is proportional to $t_ks_k$. Summing over stages gives $q_j\propto\sum_kA_{jk}t_k$ with normaliser $s^{\mathsf T}t$, which rearranges to the homogeneous linear system. When $A$ is invertible the system has the unique solution $t\propto A^{-1}q$; otherwise the feasible set is a polytope, and a linear objective attains its maximum at a vertex, which is what the bound reports. A small upper bound on $t_K$ certifies that a gain arose late, just before the final clonal expansion.

## Sources

- Z. Wang, Y. Xia, L. Mills, A. N. Nikolakopoulos, N. Maeser, S. M. Dehm, J. M. Sheltzer, R. Sun, "Evolving copy number gains promote tumor expansion and bolster mutational diversification", Nature Communications (2024), Methods ("Allele state distribution of SSNVs in an SCNA", Eq. (3); "Estimating the upper bounds of SCNA timing", Eqs. (4)–(9) and the linear program), <https://doi.org/10.1038/s41467-024-46414-5>, PMCID PMC10918155.
