# Auto cross covariance transform of protein sequences

Let a protein of length $n$ be encoded by $p$ standardized amino-acid property scales, so residue $i$ has descriptor values $z_{1,i}, \dots, z_{p,i}$ (VaxiJen uses $p = 3$ principal-property $z$-scales). For a lag $l$ with $1 \le l \le L < n$, define the auto covariance of scale $j$ and the cross covariance of scales $j \ne k$ by

$$A_{jj}(l) = \frac{1}{n - l} \sum_{i = 1}^{n - l} z_{j,i}\, z_{j,i+l}, \qquad C_{jk}(l) = \frac{1}{n - l} \sum_{i = 1}^{n - l} z_{j,i}\, z_{k,i+l}.$$

The auto cross covariance (ACC) vector of the protein collects all $A_{jj}(l)$ and $C_{jk}(l)$ for $1 \le j, k \le p$ and $1 \le l \le L$. It has exactly $p^2 L$ components whatever the sequence length $n$ (for $p = 3$ and $L = 5$, that is $45$), so proteins of different lengths become points in one Euclidean space, ready for a standard classifier.

## Remarks

Because the $z$-scales are standardized over the amino acids, the lagged products are uncentered sample covariances of property values between residues $l$ positions apart, averaged over the $n - l$ available pairs. Auto terms capture periodic or clustered patterns in one property; cross terms are not symmetric, $C_{jk}(l) \ne C_{kj}(l)$ in general, because they record which property precedes which along the chain. Short lags ($L = 5$) describe local sequence order that alignment-based similarity misses for proteins with little sequence identity. VaxiJen fits a two-class partial-least-squares discriminant model on these $45$ features to separate protective antigens from non-antigens.

## Sources

- I. A. Doytchinova, D. R. Flower, "VaxiJen: a server for prediction of protective antigens, tumour antigens and subunit vaccines", BMC Bioinformatics 8 (2007) 4, Methods, "Auto cross covariance (ACC) pre-processing", Eqns. (1)-(2). <https://doi.org/10.1186/1471-2105-8-4> (PMC1780059)
