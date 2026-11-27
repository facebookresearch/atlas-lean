# Squaring permutes the quadratic residues modulo a Blum integer

If $N = pq$ is a Blum integer, then every quadratic residue modulo $N$ has exactly four square roots, exactly one of which is itself a quadratic residue; hence $x \mapsto x^2$ is a permutation of $\mathcal{QR}_N$. Moreover $-1 \in \mathcal{QNR}_N^{+1}$, so $|\mathcal{QR}_N| = |\mathcal{QNR}_N^{+1}| = \varphi(N)/4$.

## Proof sketch

For a prime $p \equiv 3 \pmod 4$, $-1$ is a non-residue, so of the two roots $\pm r$ modulo $p$ exactly one is a residue; combine the two primes by the Chinese remainder theorem. $J_N(-1) = (-1)(-1) = 1$ while $-1$ is not a square.

## Depends on

- [Composite Jacobi symbol, pseudosquares and Blum integers](jacobi-symbol-and-blum-integers.md)

## Proof depends on

- [A square-root oracle factors pq on exactly half of the units](../../rabin-cryptosystem/two-mul-card-gcd-mem-eq-totient.md)

## Sources

- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
