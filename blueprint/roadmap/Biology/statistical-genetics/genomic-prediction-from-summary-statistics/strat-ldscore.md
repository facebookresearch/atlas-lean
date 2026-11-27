# Stratified LD score

Let $X$ be a real $N \times M$ matrix, let $C \subseteq \{1, \dots, M\}$ be a set of markers and let $j$ be a marker. The stratified LD score of $j$ with respect to $C$ is (Finucane et al. 2015)

$$\ell(j, C) = \sum_{k \in C} r_{jk}^2, \qquad r_{jk} = \frac{1}{N} \sum_{i=1}^{N} X_{ij} X_{ik},$$

with the convention $x/0 = 0$ when $N = 0$. For a standardized genotype matrix with $N > 0$, $r_{jk}$ is the sample correlation of markers $j$ and $k$.

## Sources

- H. K. Finucane et al., *Partitioning heritability by functional annotation using genome-wide association summary statistics*, Nat. Genet. 47 (2015), 1228–1235.
