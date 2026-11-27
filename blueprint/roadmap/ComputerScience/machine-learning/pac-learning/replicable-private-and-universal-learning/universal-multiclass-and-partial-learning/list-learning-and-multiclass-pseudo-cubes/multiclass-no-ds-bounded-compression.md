# Multiclass learnability does not imply DS-bounded sample compression

There is no function $f : \mathbb{N} \to \mathbb{N}$ such that every class $H \subseteq Y^X$ of DS dimension $d$ admits a sample compression scheme of size $f(d)$ independent of the sample size. Explicitly, there is a class $H \subseteq \{0, 1, 2, \dots\}^X$ of DS dimension $1$ (in particular PAC learnable) such that every sample compression scheme for $H$ compressing samples of size $m$ to $k(m)$ examples has $k(m) = \Omega\big((\log m)^{1-o(1)}\big)$. This contrasts with the binary case, where every class of VC dimension $d$ admits a compression scheme of size depending only on $d$.

## Proof sketch

Start from the partial concept class of VC (and DS) dimension one of Alon, Hanneke, Holzman and Moran, every compression scheme of which has size $\Omega((\log m)^{1-o(1)})$. Disambiguate it to a total multiclass class by replacing the undefined values of each concept by a fresh label used by no other concept; this keeps the DS dimension at one. A compression scheme for a disambiguation is also one for the partial class, so the lower bound transfers. The DS-dimension upper bound of the class guarantees learnability, so learnability and bounded compression separate.

## Depends on

- [k-pseudo-cubes and the k-DS dimension](k-pseudo-cube.md)

## Proof depends on

- [Quantitative multiclass PAC bounds from the DS dimension](ds-dimension-sample-complexity.md)
- [Sample compression for partial classes: logarithmic size suffices and is necessary](../partial-concept-classes-and-disambiguation/partial-class-sample-compression.md)

## Sources

- C. Pabbaraju, "Multiclass Learnability Does Not Imply Sample Compression", ALT (2024), arXiv:2308.06424, Theorem 1, Proposition 3.2 and Lemma 3.3.
