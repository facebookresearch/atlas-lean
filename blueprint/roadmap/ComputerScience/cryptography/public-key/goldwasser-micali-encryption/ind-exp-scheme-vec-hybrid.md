# One hybrid step

Let $u$ and $v$ be $\ell$-bit messages that differ exactly at position $j$. For every distinguisher
$D$, the [indistinguishability experiments](../../security-games/semantic-security-and-indistinguishability/ind-exp.md) of the [$\ell$-bit scheme](scheme-vec.md) on
$u$ and on $v$ are the worlds $0$ and $1$ of the [residuosity experiment](qr-exp.md) for the
[hybrid reduction](hybrid-reduction.md) built from $D$, $u$ and $j$, with
[its coins](hybrid-coins.md). In world $1$ with $u_j = 1$ the component $y \cdot y x^2 = (y x)^2$ is
an encryption of $0$ because $y x$ is uniform when $x$ is.

## Informally uses

- [The `ℓ`-bit experiment with one coordinate resampled](ind-exp-scheme-vec-eq.md)

## Sources

- S. Goldwasser and S. Micali, "Probabilistic encryption & how to play mental poker keeping secret all partial information", Proc. 14th ACM STOC (1982), 365-377, Section 4, proof of Theorem 3 (adjacent signatures).
