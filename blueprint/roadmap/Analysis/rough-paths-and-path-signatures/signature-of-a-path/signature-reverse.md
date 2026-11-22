# Time-reversed signature, coordinate form

Let every component of the velocity of $X$ be continuous, and let
$\overleftarrow{X}_u = X_{a+b-u}$ be its time reversal on $[a, b]$. Then for every word,

$$S(\overleftarrow{X})^{i_1 \cdots i_k}_{a,b} = (-1)^k\, S(X)^{i_k \cdots i_1}_{a,b}.$$

For instance $S(\overleftarrow{X})^{12}_{a,b} = S(X)^{21}_{a,b}$. Together with
[the algebraic form](tensor-mul-signature-reverse.md) this identifies the inverse of a signature
as its image under the antipode $e_{i_1} \cdots e_{i_k} \mapsto (-1)^k e_{i_k} \cdots e_{i_1}$.

## Sources

- I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine learning*,
  arXiv:1603.03788v2, Theorem 1.25, equation (22).
