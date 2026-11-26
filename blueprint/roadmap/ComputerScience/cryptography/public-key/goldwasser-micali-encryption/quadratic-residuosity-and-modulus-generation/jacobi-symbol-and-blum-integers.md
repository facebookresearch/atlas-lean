# Composite Jacobi symbol, pseudosquares and Blum integers

For $N = pq$ with distinct odd primes, the *Jacobi symbol* of a unit $x$ is $J_N(x) = \left(\frac{x}{p}\right)\left(\frac{x}{q}\right)$, computable in polynomial time without the factorization. Let $\mathcal{J}_N^{+1}$ be the units with symbol $+1$, $\mathcal{QR}_N$ the squares, and $\mathcal{QNR}_N^{+1} = \mathcal{J}_N^{+1} \setminus \mathcal{QR}_N$ the *pseudosquares*. $N$ is a *Blum integer* if $p \equiv q \equiv 3 \pmod 4$. The *quadratic residuosity assumption* states that a uniform element of $\mathcal{QR}_N$ and a uniform element of $\mathcal{QNR}_N^{+1}$ are computationally indistinguishable given $N$.

## Depends on

- [The residuosity experiment](../qr-exp.md)
- [RSA key](../../rsa-cryptosystem/key.md)

## Sources

- S. Goldwasser and S. Micali, "Probabilistic Encryption", Journal of Computer and System Sciences 28(2), 1984.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
- K. Ireland and M. Rosen, "A Classical Introduction to Modern Number Theory", 2nd edition, Graduate Texts in Mathematics 84, Springer, 1990.
