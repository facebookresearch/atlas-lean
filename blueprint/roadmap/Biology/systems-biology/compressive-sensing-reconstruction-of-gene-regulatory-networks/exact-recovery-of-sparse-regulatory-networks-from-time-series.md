# Exact recovery of sparse regulatory networks from time series

**Model.** Concentrations $x \in \mathbb R^n$ obey $\dot x = S_q F_b(x) + v + w$, where $F_b(x) \in \mathbb R^N$ stacks $N$ candidate basis functions (for example $x_j$, $x_j^{n}/(1 + x_j^{n})$, $1/(1 + x_j^{n})$), the influence map $S_q \in \mathbb R^{n \times N}$ is sparse, $v$ represents hidden nodes and $w$ noise. Sampling derivatives at times $t_1, \dots, t_M$ gives, for each gene $i$,

$$y_i = \Phi\, q_i + v_i + w_i, \qquad \Phi = \begin{pmatrix} F_b(x(t_1))^\top \\ \vdots \\ F_b(x(t_M))^\top \end{pmatrix} \in \mathbb R^{M \times N},$$

where $q_i$ is the $i$-th row of $S_q$ (the regulators of gene $i$). Stacking all genes gives one system $Z = \Omega q$ with $q = (q_1^\top, \dots, q_n^\top)^\top$.

**Proposition (uniqueness).** If every set of $2s$ columns of an $m \times N'$ sensing matrix $\Omega$ is linearly independent (possible only if $m \ge 2s$), then every $s$-sparse $q$ is the unique $s$-sparse solution of $Z = \Omega q$, namely $q = \arg\min \{\lVert q' \rVert_0 : \Omega q' = Z\}$.

**Recovery by $\ell_1$ minimisation.** Since $\ell_0$ minimisation is NP-hard, $q$ is recovered by

$$\min_q \lVert q \rVert_1 \quad \text{subject to} \quad \tilde Z = \tilde\Omega q, \qquad \tilde Z = PZ,\ \tilde\Omega = P\Omega,$$

where $P$ is a transformation chosen to lower the coherence

$$\mu(\tilde\Omega) = \max_{j \ne k} \frac{|\langle \tilde\omega_j, \tilde\omega_k\rangle|}{\lVert\tilde\omega_j\rVert\,\lVert\tilde\omega_k\rVert}$$

of the columns $\tilde\omega_j$. By the standard coherence bound, $\ell_1$ minimisation recovers every $s$-sparse $q$ exactly when $s < \tfrac12\big(1 + 1/\mu(\tilde\Omega)\big)$. Solving all genes jointly requires only $M n \ge 2\sum_i \lVert q_i\rVert_0$ rather than $M \ge 2\max_i\lVert q_i \rVert_0$ per gene, reducing the number of time points needed. Repeating identical experiments does not lower coherence; new informative perturbations do. With hidden nodes affecting few genes and sparse gross errors, exact recovery still holds under analogous conditions via robust error-correction formulations.

## Expansion

If $\Omega q_1 = \Omega q_2$ for two distinct $s$-sparse vectors, then $q_1 - q_2$ is a non-zero $2s$-sparse vector in the null space, a linear dependence among $2s$ columns, contradicting the hypothesis. Coherence controls the spark: every set of fewer than $1 + 1/\mu$ columns is linearly independent (Gershgorin applied to the Gram matrix), which yields the $\ell_1$ guarantee. Gene-network sensing matrices built from correlated basis functions along one trajectory are typically highly coherent; rearranging and multiplying the per-time-step dictionaries by suitable matrices spreads the column directions and lowers coherence, and the coherence distribution of candidate experiments indicates which additional measurements would make the network identifiable.

## Sources

- Y. H. Chang, J. W. Gray, C. J. Tomlin, "Exact reconstruction of gene regulatory networks using compressive sensing", BMC Bioinformatics 15 (2014) 400, Methods (model Eqs. 7–11; Proposition 1 and $\ell_0$ problem Eq. 2; coherence reduction by transformation, Eq. 24) and Results (Proposition 2 with proof, $\ell_1$ program Eq. 17; stacked experiments, Eq. 16; hidden nodes and noise), <https://doi.org/10.1186/s12859-014-0400-4> (PMC4308013).
- D. L. Donoho, M. Elad, "Optimally sparse representation in general (nonorthogonal) dictionaries via $\ell^1$ minimization", Proceedings of the National Academy of Sciences 100 (2003) 2197–2202, <https://doi.org/10.1073/pnas.0437847100>.
