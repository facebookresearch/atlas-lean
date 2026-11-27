# Square roots modulo a prime p ≡ 3 (mod 4)

Let $p$ be a prime with $p \equiv 3 \pmod 4$ and let $m$ be a square in $\mathbb{Z}/p\mathbb{Z}$. Then

$$\left(m^{(p+1)/4}\right)^2 = m.$$

For $m \ne 0$ this is Euler's criterion $m^{(p-1)/2} = 1$, since
$m^{(p+1)/2} = m \cdot m^{(p-1)/2}$; for $m = 0$ both sides vanish. This is how the owner of the
private key inverts the Rabin function when $p \equiv q \equiv 3 \pmod 4$: square roots modulo $p$
and modulo $q$, combined by the Chinese remainder theorem.

Rabin states the formula for quadratic residues $m$ (nonzero); the statement here also covers
$m = 0$.

## Sources

- M. O. Rabin, *Digitalized signatures and public-key functions as intractable as factorization*, MIT/LCS/TR-212, MIT Laboratory for Computer Science, January 1979, Section 2, equation (2).
