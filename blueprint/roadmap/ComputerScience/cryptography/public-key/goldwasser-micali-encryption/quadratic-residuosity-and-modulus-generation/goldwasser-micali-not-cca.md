# Goldwasser–Micali encryption is malleable and not CCA secure

In Goldwasser–Micali encryption ($c = z^{b} r^2 \bmod N$ for a bit $b$, uniform unit $r$ and public pseudosquare $z$), multiplying a ciphertext by $z$ flips the encrypted bit and multiplying by a fresh square rerandomizes it. Hence the scheme is not CCA secure: given the challenge $c^*$, the adversary asks for the decryption of $z c^* \ne c^*$ and learns $1 - b$. With the textbook key generation drawing $z$ uniformly from $\mathcal{QNR}_N^{+1}$, the scheme is IND-CPA under the quadratic residuosity assumption.

## Proof sketch

$z \cdot z^b r^2 = z^{b+1} r^2$ and $z^2$ is a square, so $z^{b+1}r^2$ is an encryption of $b \oplus 1$. CPA security is the standard residuosity reduction with a uniformly sampled pseudosquare key.

## Depends on

- [Composite Jacobi symbol, pseudosquares and Blum integers](jacobi-symbol-and-blum-integers.md)
- [The Goldwasser–Micali scheme for $\ell$-bit messages](../scheme-vec.md)
- [Public-key CCA experiment](../../../security-games/generic-security-games/pub-cca-game.md)

## Sources

- S. Goldwasser and S. Micali, "Probabilistic Encryption", Journal of Computer and System Sciences 28(2), 1984.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
