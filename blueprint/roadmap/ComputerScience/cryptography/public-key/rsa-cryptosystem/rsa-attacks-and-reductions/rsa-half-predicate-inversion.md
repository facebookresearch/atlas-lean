# An oracle for the RSA half predicate inverts RSA

(a) For an odd modulus $N \le 2^m$ and $x < N$, the values of $P_x(r) = [\,x r \bmod N > N/2\,]$ at $r = 2^0, 2^1, \dots, 2^{m-1}$ determine $x$, and $x$ is computable from them in polynomial time; oddness is necessary. (b) Given an oracle that decides, for an RSA image $w^e \bmod N$, whether $w > N/2$, the algorithm that queries the images $2^{ke}\,y = (2^k x)^e$ of $2^k x$ for $k < m$ recovers the preimage $x$ of $y$. Thus computing the half (equivalently, the least significant) bit of RSA preimages is as hard as inverting RSA.

## Proof sketch

Doubling modulo an odd $N$ wraps around exactly when the current value exceeds $N/2$, so the sequence of half bits gives the binary expansion of $x/N$ to precision $2^{-m}$, which determines $x$. The RSA images of $2^k x$ are computable from $y$ by multiplicativity.

## Depends on

- [RSA-inversion experiment](../../hardness-assumptions/rsa-game.md)
- [Malleability of textbook RSA](../../insecurity-of-textbook-rsa/encrypt-mul.md)

## Sources

- W. Alexi, B. Chor, O. Goldreich and C.-P. Schnorr, "RSA and Rabin Functions: Certain Parts Are as Hard as the Whole", SIAM Journal on Computing 17(2), 1988.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
