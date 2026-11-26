# Categorical likelihood for complexity of infection and allele frequencies

Let $n$ hosts be genotyped at $k$ biallelic loci. Host $i$ carries $m_i \in \{1, 2, \dots\}$
independent parasite lineages (its complexity of infection, COI) and locus $j$ has population
major-allele frequency $p_j \in (0,1)$. Assume loci, hosts and the lineages within a host are
independent draws from one homogeneous population. The true call $B^T_{ij} \in \{0, 0.5, 1\}$
(homozygous minor, heterozygous, homozygous major) has

$$P(B^T_{ij} \mid m_i, p_j) =
\begin{cases}
p_j^{m_i} & B^T_{ij} = 1,\\
(1-p_j)^{m_i} & B^T_{ij} = 0,\\
1 - p_j^{m_i} - (1-p_j)^{m_i} & B^T_{ij} = 0.5 .
\end{cases}$$

The observed call $B^O_{ij}$ differs from the truth through error probabilities $e_1$ (a
homozygous locus called heterozygous) and $e_2$ (a heterozygous locus called homozygous), giving an
error matrix $P(B^O_{ij} \mid B^T_{ij})$. The likelihood of $M = (m_1,\dots,m_n)$ and
$P = (p_1,\dots,p_k)$ is

$$L(M, P \mid B^O) = \prod_{i=1}^{n}\prod_{j=1}^{k} \sum_{b \in \{0, 0.5, 1\}}
P(B^O_{ij} \mid B^T_{ij} = b)\, P(B^T_{ij} = b \mid m_i, p_j),$$

and with uniform priors $M$ and $P$ (and optionally $e_1$, $e_2$) are sampled jointly by
Metropolis–Hastings.

## Expansion

A host is homozygous for the major allele at a locus only if all $m_i$ lineages carry it, which
has probability $p_j^{m_i}$, and similarly for the minor allele; heterozygosity is the complement.
Estimating allele frequencies from monogenomic infections alone discards most of the data in
high-transmission settings, while estimating COI with allele frequencies fixed in advance
propagates their error. Sampling both in one chain lets polygenomic infections inform the allele
frequencies and accounts for the uncertainty of each in the other. Larger $m_i$ makes
heterozygous calls more likely at every locus, which is what identifies COI.

## Sources

- H.-H. Chang, C. J. Worby, A. Yeka, J. Nankabirwa, M. R. Kamya, S. G. Staedke, G. Dorsey,
  M. Murphy, D. E. Neafsey, A. E. Jeffreys, C. Hubbart, et al., "THE REAL McCOIL: A method for the
  concurrent estimation of the complexity of infection and SNP allele frequency for malaria
  parasites", PLoS Computational Biology 13 (2017) e1005348, Materials and Methods,
  "Categorical method" (Eqs. 1-2, Table 1), <https://doi.org/10.1371/journal.pcbi.1005348>
  (PMC5300274).
