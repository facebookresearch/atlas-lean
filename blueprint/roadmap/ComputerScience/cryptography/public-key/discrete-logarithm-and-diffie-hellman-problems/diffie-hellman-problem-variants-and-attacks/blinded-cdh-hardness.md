# Hardness of the blinded Diffie–Hellman problems

Write $[u, v]$ for the Diffie–Hellman value of $u = g^x, v = g^y$, i.e. $g^{xy}$. In a prime-order group family satisfying CDH: (a) given uniform $a, b, u, v \in G$, no efficient adversary outputs $\gamma \in \mathbb{Z}_q$ and $w = [u / a^{\gamma},\, v / b^{\gamma}]$ with non-negligible probability; (b) given uniform $a, b, u$, no efficient adversary outputs $\gamma_1 \ne \gamma_2$, an element $v$, and $w_i = [u/a^{\gamma_i}, v/b^{\gamma_i}]$ for $i = 1, 2$ with non-negligible probability. These are the problems arising in the analysis of password-authenticated key exchange.

## Proof sketch

Expanding $[u/a^\gamma, v/b^\gamma]$ bilinearly writes it as $[u,v]$ times known powers of $[a, v], [u, b], [a, b]$. Embedding a CDH instance into $u, v$ (part (a)), or exploiting two values $\gamma_1 \ne \gamma_2$ to cancel the unknown cross terms (part (b)), and applying the list form of CDH to the remaining candidates recovers a CDH solution.

## Depends on

- [Computational Diffie–Hellman experiment](../../hardness-assumptions/cdh-game.md)

## Proof depends on

- [Under CDH, no efficient adversary lists the Diffie–Hellman value among polynomially many candidates](list-cdh-hardness.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
