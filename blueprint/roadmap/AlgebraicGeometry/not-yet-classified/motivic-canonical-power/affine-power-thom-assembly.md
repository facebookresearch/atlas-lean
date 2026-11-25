# Affine Power Thom Assembly

Thom data for powers of affine cycles: over a perfect field $k$, for the given motivic interface
data (whose comparison maps
$\mathbb{Z}_{tr}(\mathbb{A}^m)/\mathbb{Z}_{tr}(\mathbb{A}^m - 0) \otimes M \to K(M(m), 2m)$ are
assumed to be motivic weak equivalences, natural in $M$, multiplicative and normalized in rank one),
a free quotient `U` of a finite group $H$ with affine base, a permutation representation
$r : H → S_n$, $i \in \mathbb{N}$ and a ring $R$, every finite correspondence $z$ with coefficients
in $R$ from a smooth affine $k$-scheme $X$ to the affine space $\mathbb A^i$ of `A` is the input of
a `FinitePowerThomTest` on $X$: a power quotient with its cycle descent and diagonal, the
pulled-back power bundle and its complement, and a Thom class whose Thom action is bijective,
assembled for $z$.
