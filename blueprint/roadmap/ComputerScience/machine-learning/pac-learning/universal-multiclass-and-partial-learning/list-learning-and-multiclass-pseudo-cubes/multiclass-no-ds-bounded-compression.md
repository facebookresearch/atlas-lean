# Multiclass learnability does not imply DS-bounded sample compression

There is no function $f : \mathbb{N} \to \mathbb{N}$ such that every class $H \subseteq Y^X$ of DS dimension $d$ admits a sample compression scheme of size $f(d)$ independent of the sample size. Explicitly, for every $f$ there is a class of DS dimension $1$ (in particular PAC learnable) all of whose sample compression schemes on samples of size $n$ have size growing to infinity with $n$. This contrasts with the binary case, where every class of VC dimension $d$ admits a compression scheme of size depending only on $d$.

## Proof sketch

The construction uses the classes of Natarajan dimension one with large pseudo-cubes and a counting argument: a compression scheme of size $r$ on $n$ points has at most $\binom{n}{\le r}$ reconstruction patterns per label sequence, while the projection of a suitably chosen DS-dimension-one class onto $n$ points has too many realizable labelings with large label sets to be reconstructed from so few patterns. The DS-dimension upper bound of the class guarantees learnability, so learnability and bounded compression separate.

## Depends on

- [Quantitative multiclass PAC bounds from the DS dimension](ds-dimension-sample-complexity.md)

## Proof depends on

- [Quantitative multiclass PAC bounds from the DS dimension](ds-dimension-sample-complexity.md)

## Sources

- C. Pabbaraju, "Multiclass Learnability Does Not Imply Sample Compression", ALT (2024), arXiv:2308.06424.
