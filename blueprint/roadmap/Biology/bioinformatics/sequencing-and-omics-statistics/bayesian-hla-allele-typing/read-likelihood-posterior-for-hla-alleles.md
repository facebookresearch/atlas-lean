# Read-likelihood posterior for HLA allele typing

Fix one HLA gene with candidate alleles $a_1, \dots, a_{N_A}$ (full genomic sequences), population prior frequencies $f_m$ for the sample's inferred ancestry, and $N$ read pairs $r_1, \dots, r_N$ aligned to at least one allele, $N_m$ of them to allele $a_m$. For a base of Phred quality $q_i$ let $e_i = 10^{-q_i/10}$ be its error probability and model the observed base as one multinomial draw with

$$\alpha_{B,i} = \begin{cases} 1 - e_i & \text{if the base of } a_m \text{ at that position is } B, \\ e_i / 3 & \text{otherwise.} \end{cases}$$

Assuming independence of positions, reads and insert sizes, the likelihood of read pair $r_k$ (read lengths $l_{k1}, l_{k2}$, insert size $d_k$) given allele $a_m$ is

$$P(r_k \mid a_m) = \begin{cases} \displaystyle\prod_{i=1}^{l_{k1}} \alpha_i \prod_{j=1}^{l_{k2}} \alpha_j \cdot P(D = d_k) & \text{if } r_k \text{ aligns to } a_m, \\ s_k & \text{otherwise,} \end{cases}$$

where $P(D = d_k)$ is the empirical insert-size frequency in the whole run and $s_k$ is the smallest probability achievable by a pair of the same lengths with maximal base quality $93$, i.e. $\ln s_k = (l_{k1} + l_{k2}) \ln\bigl(10^{-9.3} / 3\bigr) \approx -22.5\,(l_{k1} + l_{k2})$ (rounded to $-23$ in the source). The posterior is

$$P(a_m \mid r_1, \dots, r_N) = \frac{f_m \prod_{k=1}^{N} P(r_k \mid a_m)}{\prod_{k=1}^{N} P(r_k)},$$

and up to terms common to all alleles its logarithm is

$$L_m = \sum_{k \to a_m} \Bigl(\sum_{i} \ln \alpha_i + \sum_{j} \ln \alpha_j + \ln P(D = d_k)\Bigr) + (N - N_m)\, s'_k + \ln f_m,$$

with the first sum over the $N_m$ pairs aligned to $a_m$ and $s'_k = \ln s_k$. The **first allele** is $a_w = \arg\max_m L_m$. For the **second allele**, each read pair aligned both to $a_m$ and to the winner is down-weighted by $l_{mk} / (l_{mk} + l_{wk})$, where $l_{mk}, l_{wk}$ are its likelihoods under $a_m$ and $a_w$ (pairs aligned to $a_m$ but not to $a_w$ keep weight $1$), and the allele with the largest re-weighted score is chosen.

## Expansion

The model is a naive-Bayes classifier over alleles: base calls contribute through their quality-calibrated error rates, unaligned reads contribute a fixed worst-case penalty so that alleles explaining more reads are favored, and the ancestry-specific prior breaks ties among near-identical alleles. Terms such as $N \ln s_k$ and $\sum_k \ln P(r_k)$ are the same for every allele and cancel in the argmax. Because HLA alleles differ at few positions, reads supporting the first allele also align to its close relatives; the re-weighting step removes that shared support so the second call reflects reads the first allele explains poorly. With alleles called per sample, tumor and normal reads realigned to the patient's own HLA sequences allow somatic mutation calling in a region where reference-based alignment fails.

## Sources

- S. A. Shukla, M. S. Rooney, M. Rajasagi, G. Tiao, P. M. Dixon, M. S. Lawrence et al., "Comprehensive analysis of cancer-associated somatic mutations in class I HLA genes", Nature Biotechnology (2015), Online Methods "Allele inference" and "Ethnicity inference and prior probability estimation", <https://doi.org/10.1038/nbt.3344>, PMCID PMC4747795.
