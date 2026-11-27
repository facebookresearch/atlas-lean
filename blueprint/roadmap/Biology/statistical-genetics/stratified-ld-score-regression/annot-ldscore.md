# Annotation LD score of a marker

Let $X$ be a real $N \times M$ genotype matrix and let $a = (a_{kC})$ assign to each marker $k$ and each annotation $C$ (in an arbitrary index set) a real value. The LD score of marker $j$ with respect to annotation $C$ is

$$\ell(j, C) = \sum_{k=1}^{M} a_{kC}\, r_{jk}^2, \qquad r_{jk} = \frac{1}{N} \sum_{i=1}^{N} X_{ij} X_{ik},$$

with the convention $x/0 = 0$ when $N = 0$. Binary annotations give the stratified LD scores of Finucane et al. (2015); continuous annotations are allowed, as in Gazal et al. (2017).

## Sources

- H. K. Finucane, B. Bulik-Sullivan, A. Gusev, G. Trynka, Y. Reshef, P.-R. Loh, et al., *Partitioning heritability by functional annotation using genome-wide association summary statistics*, Nat. Genet. 47 (2015), 1228–1235.
- S. Gazal, H. K. Finucane, N. A. Furlotte, P.-R. Loh, P. F. Palamara, X. Liu, et al., *Linkage disequilibrium–dependent architecture of human complex traits shows action of negative selection*, Nat. Genet. 49 (2017), 1421–1427.
