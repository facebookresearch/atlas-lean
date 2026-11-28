# Cyclic shift permutation test for recurrent aberrations

**Setting.** Data from $n$ subjects at $m$ common genomic markers form an $n \times m$ matrix $\mathbf X$ with entries in $\mathcal A \subseteq \mathbb R$ (copy number, methylation level, association statistic). For each marker $j$ a local statistic $s_j = s_j(\mathbf X_{\cdot j})$ is computed, typically the column sum $s_j = \sum_{i=1}^n x_{ij}$, and a global statistic such as

$$T(\mathbf X) = \max(s_1, \dots, s_m)$$

summarizes the strongest coordinated departure from baseline (a minimum is used for losses). Because $T$ is a maximum over markers, no further multiplicity correction is needed.

**Cyclic shifts.** For $k \in \{0, \dots, m-1\}$ the cyclic shift of index $k$ is

$$\sigma_k(x_1, \dots, x_m) = (x_{k+1}, \dots, x_m, x_1, \dots, x_k).$$

For $\mathbf k = (k_1, \dots, k_n)$, $\sigma_{\mathbf k}(\mathbf X)$ applies $\sigma_{k_i}$ to row $i$. The set of all cyclic shifts of $\mathbf X$ is $\mathcal S_m(\mathbf X) = \{\sigma_{\mathbf k}(\mathbf X) : \mathbf k \in \{0, \dots, m-1\}^n\}$.

**Procedure.** Draw $N$ random shifts $\sigma^1, \dots, \sigma^N$ with $k_1, \dots, k_n$ independent and uniform on $\{0, \dots, m-1\}$, and report

$$p(T(\mathbf X)) = \max\Bigl(N^{-1} \sum_{l=1}^N \mathbf 1\{T(\sigma^l(\mathbf X)) \ge T(\mathbf X)\},\ 1/N\Bigr).$$

As $N \to \infty$ this converges in probability to $Q_{\mathbf X}(T \ge T(\mathbf X))$, where the *cyclic conditional distribution* $Q_{\mathbf X}$ is the uniform distribution on $\mathcal S_m(\mathbf X)$; when the $m^n$ shifts are distinct, $Q_{\mathbf X}(A) = m^{-n} |A \cap \mathcal S_m(\mathbf X)|$.

**Invariance.** A statistic $T$ is *invariant under constant shifts* if $T(\mathbf X) = T(\mathbf X')$ whenever $\mathbf X'$ is obtained by applying the same $\sigma_k$ to every row. Every statistic $T(\mathbf X) = g(h(\mathbf X_{\cdot 1}), \dots, h(\mathbf X_{\cdot m}))$ with an arbitrary local map $h$ and a cyclically invariant $g$ (in particular the maximum column sum) has this property.

## Expansion

Full permutation of all entries destroys both within-sample correlation and between-sample differences in scale or location, and row-by-row permutation (as in GISTIC) still destroys the serial correlation along each genome; either can declare markers significant when only such secondary features are present. A cyclic shift keeps each sample's sequence intact except for one break point, so serial correlation and per-sample distribution are preserved, while independent offsets across samples break the alignment of markers that a true recurrent aberration would create. The test therefore targets exactly the coordinated, location-specific signal.

## Sources

- V. Walter, F. A. Wright, A. B. Nobel, "Consistent Testing for Recurrent Genomic Aberrations", arXiv:1403.1876 (2014), Section 2 (Data Matrix, Cyclic Shift Testing, Testing Framework, Principal Result). <https://doi.org/10.48550/arXiv.1403.1876>
