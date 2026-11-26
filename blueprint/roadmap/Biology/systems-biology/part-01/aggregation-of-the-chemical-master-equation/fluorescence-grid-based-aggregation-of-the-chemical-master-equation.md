# Fluorescence grid based aggregation of the chemical master equation

Consider a gene that switches among $G$ phases (for the epigenetically phase-varying *agn43* gene of *E. coli*, $G=5$: fully methylated, hemimethylated, unmethylated, unmethylated with OxyR bound, and Off), producing protein at phase-dependent rates and with protein diluted by cell division at rate $\gamma$. Order the configurations (protein number $x$, phase) as consecutive blocks of $G$ entries for $x=0,1,2,\dots$. The configuration probabilities satisfy the chemical master equation $\dot P=AP$ with block-tridiagonal generator

$$
A=\begin{pmatrix}K-B&\gamma I&0&\cdots\\ B&K-B-\gamma I&2\gamma I&\\ 0&B&K-B-2\gamma I&3\gamma I\\ \vdots&&\ddots&\ddots\end{pmatrix},
$$

where $K$ is the phase-switching rate matrix (any matrix with zero column sums) and $B=\operatorname{diag}(\beta_{\mathrm{phase}})$ holds the protein production rates.

**Aggregation.** Lump the protein numbers into consecutive groups of sizes $m_1,m_2,\dots$ (keeping phases separate) with aggregation operator $E$ (block row sums) and disaggregation operator $F$ (uniform redistribution, weight $1/m_i$ within group $i$). The approximate aggregated chain $\dot P_a=EAFP_a$, $P_a(0)=EP(0)$, has generator

$$
EAF=\begin{pmatrix}K-\tfrac1{m_1}B&0&\cdots\\ \tfrac1{m_1}B&K-\tfrac1{m_2}B&\\ 0&\tfrac1{m_2}B&\ddots\end{pmatrix}+\begin{pmatrix}0&\tfrac{\gamma m_1}{m_2}I&0&\cdots\\ 0&-\tfrac{\gamma m_1}{m_2}I&\tfrac{\gamma(m_1+m_2)}{m_3}I&\\ 0&0&-\tfrac{\gamma(m_1+m_2)}{m_3}I&\ddots\end{pmatrix}.
$$

**Theorem (FGBA).** Let fluorescence be proportional to protein number with unknown ratio $\mu$, let $\Delta_1,\Delta_2,\dots$ be the bin widths of the experimental fluorescence histogram, and let $B_f$ be $B$ with each rate replaced by its fluorescence-based counterpart $\beta_f=\mu\beta$. Choosing group sizes with $\mu m_i\simeq\Delta_i$, the aggregated chain becomes the fluorescence-based master equation $\dot P_f=A_fP_f$, with $A_f$ obtained from $EAF$ by replacing $B/m_i$ with $B_f/\Delta_i$ and $(m_1+\dots+m_{i-1})/m_i$ with $(\Delta_1+\dots+\Delta_{i-1})/\Delta_i$. Its solution simulates the experimental fluorescence histogram directly: the $i$-th block of $P_f(t)$ is the probability that a cell's fluorescence lies in the $i$-th histogram bin, and the unknown $\mu$ and $m_i$ no longer appear.

## Expansion

The aggregation is regular (linear and state-partitioning) but not lumpable, so $P_a$ only approximates $EP$; the uniform-within-bin assumption is reasonable when the protein distribution is smooth on the logarithmically spaced histogram bins. Under $\mu m_i=\Delta_i$ one has $\beta/m_i=\beta_f/\Delta_i$ and $(m_i+m_j)/m_k=(\Delta_i+\Delta_j)/\Delta_k$, which converts the protein-number model into a model in fluorescence units whose size equals the number of histogram bins times $G$. This removes the dependence on unmeasured production rates, makes the model comparable with flow cytometry data bin by bin, and shrinks the state space. For a single phase, the error in the mean of the aggregated distribution can be bounded in terms of the bin-growth ratio $\max\Delta_i/\Delta_{i-1}$ and the mismatch $\max|\mu m_i-\Delta_i|$.

## Sources

- A. Mirtabatabaei, F. Bullo, M. Khammash, "Flow Cytometry Based State Aggregation of a Stochastic Model of Protein Expression", Section 3 (Theorem 3.1, Proposition 3.2). <https://doi.org/10.48550/arXiv.1104.1803>
