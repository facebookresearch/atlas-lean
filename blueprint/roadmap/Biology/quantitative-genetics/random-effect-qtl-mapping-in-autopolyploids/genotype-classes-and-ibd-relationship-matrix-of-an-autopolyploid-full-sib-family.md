# Genotype classes and IBD relationship matrix of an autopolyploid full-sib family

Let $m \ge 2$ be even and consider a cross between two autopolyploid parents of ploidy $m$ whose $2m$ homologous copies at a locus carry distinct labels ($a, b, \dots$ in one parent, $g, h, \dots$ in the other). Under random bivalent pairing, each parent transmits a gamete consisting of $m/2$ of its $m$ copies, every such subset with equal probability.

**Proposition.**

1. Each parent produces $\binom{m}{m/2}$ equally likely gametes, and the full-sib family has $p = \binom{m}{m/2}^2$ equally likely genotype classes at the locus: $p = 36$ for tetraploids, $p = 400$ for hexaploids and $p = 4900$ for octoploids.
2. Define the $p \times p$ matrix $\Pi$ by $\Pi_{jj'} = (\text{number of labelled copies shared by genotypes } j \text{ and } j')/m$. Then $\Pi_{jj} = 1$, $\Pi_{jj'} \in \{0, 1/m, \dots, 1\}$, and $\Pi$ is positive semidefinite: writing $\mathbf 1_j \in \{0,1\}^{2m}$ for the indicator of the copies in genotype $j$, $\Pi_{jj'} = \mathbf 1_j^\top \mathbf 1_{j'}/m$.
3. For $n$ individuals with genotype conditional probabilities $Z_{ij} = \Pr(\text{individual } i \text{ has genotype } j \mid \text{map})$ at a putative QTL $q$, the IBD relationship matrix at $q$ is

$$G_q = Z_q \Pi Z_q^\top, \qquad (G_q)_{ii'} = \sum_{j,j'=1}^{p} Z_{ij} Z_{i'j'}\, \Pi_{jj'} \in [0, 1],$$

which is positive semidefinite, and $(G_q)_{ii'}$ is the expected fraction of the $m$ copies of $i$ that are identical by descent with copies of $i'$.

## Expansion

Item 1 counts subsets of size $m/2$ and uses independence of the two gametes. Item 2 is a Gram-matrix representation, hence positive semidefinite; item 3 follows because $Z_q \Pi Z_q^\top = (Z_q B)(Z_q B)^\top$ with $B$ the $p \times 2m$ matrix of rows $\mathbf 1_j^\top/\sqrt m$, and each row of $Z_q$ is a probability vector, so entries are convex combinations of numbers in $[0,1]$. For example, two sibs with known hexaploid genotypes $abcghi$ and $abcghj$ share $5$ of $6$ copies, so $(G_q)_{ii'} = 5/6$; averaging $G_q$ over the genome gives about $1$ on the diagonal and $1/2$ between full sibs.

## Sources

- G. da Silva Pereira, D. C. Gemenet, M. Mollinari et al., "Multiple QTL mapping in autopolyploids: a random-effect model approach with application in a hexaploid sweetpotato full-sib population", Genetics (2020), <https://doi.org/10.1534/genetics.120.303080>, PMCID PMC7337090 (QTL mapping analyses, definition of $\Pi$ and $G_q$).
