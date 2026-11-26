# Tumour variant log-odds score with an explicit allele fraction

Fix a genomic site with reference allele $r \in \{A, C, G, T\}$ covered by $d$ tumour reads. Read $i$ has called base $b_i$ and base-call error probability $e_i = 10^{-q_i/10}$, where $q_i$ is its Phred quality. For a candidate alternate allele $m \ne r$ and an allele fraction $f \in [0,1]$, the model $M^m_f$ says that a fraction $f$ of the DNA molecules carry $m$, and that every base call is wrong with probability $e_i$, a wrong call being each of the three other bases with probability $e_i/3$. Assuming independent errors across reads,

$$L[M^m_f] = \prod_{i=1}^{d} P(b_i \mid e_i, r, m, f), \qquad
P(b_i \mid e_i, r, m, f) = \begin{cases}
f\,\dfrac{e_i}{3} + (1-f)(1-e_i), & b_i = r,\\[4pt]
f(1-e_i) + (1-f)\,\dfrac{e_i}{3}, & b_i = m,\\[4pt]
\dfrac{e_i}{3}, & \text{otherwise.}
\end{cases}$$

The reference (noise-only) model is $M_0 = M^m_0$. The tumour log-odds score is

$$\mathrm{LOD}_T(m, f) = \log_{10}\frac{L[M^m_f]}{L[M_0]} .$$

**Decision rule.** Requiring posterior odds of at least $\delta_T$ in favour of the variant, with prior probability $P(m,f)$ of a variant, is equivalent to

$$\mathrm{LOD}_T(m, f) \ \ge\ \theta_T = \log_{10}\delta_T - \log_{10}\frac{P(m,f)}{1-P(m,f)} .$$

With $\delta_T = 2$, a uniform prior on $f$ and $P(m) = \tfrac13 \cdot 3\times 10^{-6}$ (one third of a typical somatic mutation frequency per base), $\theta_T \approx 0.3 + 6.0 = 6.3$. The score is maximized over the three alleles $m$, and $f$ is replaced by the plug-in estimate $\hat f = (\text{number of reads showing } m)/d$ instead of the exact maximizer. To guard against cross-sample contamination at level $f_{\mathrm{cont}}$, $M_0$ is replaced by $M^m_{f_{\mathrm{cont}}}$.

**Sensitivity.** For $n$ reads of common error rate $e$, let $k$ be the least alternate-read count $x$ with $\mathrm{LOD}_T(x \mid n, e) \ge \theta_T$. In the worst case where every misread reference base becomes the same alternate allele, an alternate read appears with probability $f(1-e) + (1-f)e$, so the probability of detecting a mutation at allele fraction $f$ is

$$\sum_{i=k}^{n} \binom{n}{i}\bigl(f(1-e) + (1-f)e\bigr)^{i}\bigl(1 - f(1-e) - (1-f)e\bigr)^{n-i}.$$

## Depends on

- [Power of the randomized mutation detection test](../../detection-power-for-somatic-mutations/power.md)

## Expansion

Bayes' rule gives posterior odds $= \dfrac{L[M^m_f]}{L[M_0]} \cdot \dfrac{P(m,f)}{1-P(m,f)}$; taking $\log_{10}$ and moving the prior odds to the right gives $\theta_T$. Modelling $f$ explicitly, instead of fixing a heterozygous diploid fraction $f = 1/2$, keeps power for subclonal mutations and impure samples, where the true fraction is far below $1/2$. The per-read likelihood is the two-component mixture of "molecule carries $m$" and "molecule carries $r$", each followed by the symmetric error channel. Because the score assumes independent errors and correct read placement, it predicts sensitivity well but underestimates the false-positive rate. That is why the full caller adds artifact filters and a panel of normals after this test.

## Sources

- K. Cibulskis, M. S. Lawrence, S. L. Carter, et al., "Sensitive detection of somatic point mutations in impure and heterogeneous cancer samples", Nature Biotechnology 31 (2013), Online Methods ("Variant detection", "Sensitivity calculation"), <https://doi.org/10.1038/nbt.2514> (PMC3833702).
