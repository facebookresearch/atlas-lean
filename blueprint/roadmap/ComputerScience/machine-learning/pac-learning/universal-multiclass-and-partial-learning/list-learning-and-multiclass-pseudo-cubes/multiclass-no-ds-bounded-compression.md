# Multiclass learnability does not imply DS-bounded sample compression

There is no function $f : \mathbb{N} \to \mathbb{N}$ such that every class $H \subseteq Y^X$ of DS dimension $d$ admits a sample compression scheme of size $f(d)$ independent of the sample size. Explicitly, for every $f$ there is a class of DS dimension $1$ (in particular PAC learnable) all of whose sample compression schemes on samples of size $n$ have size growing to infinity with $n$. This contrasts with the binary case, where every class of VC dimension $d$ admits a compression scheme of size depending only on $d$.

## Proof sketch

The construction lifts a partial concept class of VC dimension one that admits no compression scheme of bounded size to a total multiclass class of DS dimension one, by giving each undefined value its own fresh label; a bounded-size compression scheme for the lifted class would yield one for the partial class, and a counting argument rules this out. The DS-dimension upper bound of the class guarantees learnability, so learnability and bounded compression separate.

## Depends on

- [k-pseudo-cubes and the k-DS dimension](k-pseudo-cube.md)

## Proof depends on

- [Quantitative multiclass PAC bounds from the DS dimension](ds-dimension-sample-complexity.md)

## Sources

- C. Pabbaraju, "Multiclass Learnability Does Not Imply Sample Compression", ALT (2024), arXiv:2308.06424.
