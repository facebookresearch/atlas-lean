# Distribution uniformity of congruence-derivative matrices for tandem repeat detection

**Definitions.** Let $s=s_1\cdots s_n$ be a DNA sequence over $\{A,C,G,T\}$ and $u_\alpha(k)=1$ if $s_k=\alpha$, else $0$. For a candidate period $p$, the **congruence derivative (CD) matrix** is the $4\times p$ matrix of nucleotide counts at periodic positions,

$$f_{\alpha,j}=\sum_{k\le n,\ k\equiv j\ (\mathrm{mod}\ p)}u_\alpha(k),\qquad \alpha\in\{A,C,G,T\},\ j=1,\dots,p .$$

Its $4p$ entries sum to $n$, with mean $n/(4p)$. Define

$$DU(p)=\sum_{\alpha}\sum_{j=1}^p\Big(f_{\alpha,j}-\frac n{4p}\Big)^2,\qquad NDU(p)=\frac{DU(p)}n,\qquad CP(p)=\frac np,\qquad PR(p)=\frac1n\sum_{j=1}^p\max_\alpha f_{\alpha,j},$$

the distribution uniformity, its normalized form, the copy number and the perfect level. The column-wise most frequent nucleotides $d_j=\arg\max_\alpha f_{\alpha,j}$ spell the **consensus repeat unit** of length $p$, and the off-maximum entries of each column count mismatches against that consensus.

**Properties.** $DU(p)$ is $4p$ times the variance of the CD-matrix entries. It is small when nucleotides are spread evenly over the periodic positions (no period-$p$ structure) and large when each column is dominated by one nucleotide. If $p$ divides $n$, every column sums to $n/p$, and

$$NDU(p)\le\frac34\,\frac np=\frac34\,CP(p),$$

with equality if and only if every column is concentrated on a single nucleotide, i.e. $s$ is a perfect tandem repeat of a unit of length $p$; equivalently $PR(p)=1$. For approximate repeats, $PR(p)$ is the fraction of positions matching the consensus. Repeats and genomic periodicities are identified as the periods at which $NDU$ stands out from its background over a scan of $p$, after which the CD matrix directly gives the consensus pattern, copy number and perfect level, which a Fourier power spectrum does not.

## Expansion

The bound follows because, for a column with fixed total $n/p$, the sum of squared deviations from the constant $n/(4p)$ is maximized by putting all mass on one entry, which contributes $(3n/(4p))^2+3(n/(4p))^2=3n^2/(4p^2)$ per column, hence $3n^2/(4p)$ for $DU$. The CD matrix is a sufficient statistic for the discrete Fourier power at frequencies that are multiples of $n/p$, so the uniformity measure generalizes earlier period-3 coding signals to arbitrary periods while keeping positional information. Multiples of a true period $p$ also give large values, and the smallest such period is reported.

## Sources

- Changchuan Yin, "Identification of repeats in DNA sequences using nucleotide distribution uniformity", arXiv:1608.00567 (2016), Methods (Definitions 6.1–6.6, CD matrix example), <https://doi.org/10.48550/arXiv.1608.00567>.
