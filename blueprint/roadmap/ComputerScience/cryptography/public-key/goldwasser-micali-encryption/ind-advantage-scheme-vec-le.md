# The hybrid argument for bitwise Goldwasser–Micali encryption

For every distinguisher $D$ and all $\ell$-bit messages $m$, $m'$, the
[distinguishing advantage](../../security-games/semantic-security-and-indistinguishability/ind-advantage.md) of $D$ between encryptions of $m$ and of $m'$ under
the [$\ell$-bit scheme](scheme-vec.md) is at most

$$\sum_{j < \ell} \mathrm{Adv}^{\mathrm{QR}}\bigl(B_j\bigr),$$

where $B_j$ is the [hybrid reduction](hybrid-reduction.md) at position $j$ built from $D$ and the
[$j$-th hybrid message](hybrid-msg.md), and $\mathrm{Adv}^{\mathrm{QR}}$ is the
[residuosity advantage](qr-advantage.md). For positions where $m$ and $m'$ agree,
consecutive hybrid messages coincide and the term is not needed; the stated bound keeps it and is loose
there.

This is the concrete form of Goldwasser and Micali's Theorem 3: a decision function that tells two
"$n$-signatures" (residuosity patterns of ciphertexts) apart yields a residuosity decider, through a
pair of adjacent signatures.

## Informally uses

- [One hybrid step](ind-exp-scheme-vec-hybrid.md)

## Sources

- S. Goldwasser and S. Micali, "Probabilistic encryption & how to play mental poker keeping secret all partial information", Proc. 14th ACM STOC (1982), 365-377, Section 4, Theorem 3.
