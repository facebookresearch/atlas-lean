# Correctness of WOTS+ public-key reconstruction

For every WOTS+ key pair, message digest and address, reconstructing the public key from the honest signature returns the public key: chain end $i$ is $\mathrm{chain}(\mathrm{chain}(sk_i, 0, m_i), m_i, w - 1 - m_i) = \mathrm{chain}(sk_i, 0, w - 1)$. Every base-$2^b$ digit produced by the byte-to-base conversion lies in $[0, 2^b)$, so all chain indices are in range. The checksum makes the digit vectors of distinct messages incomparable: if $m \ne m'$ then some digit of $m$ is strictly smaller than the corresponding digit of $m'$, so a signature on one message does not yield one on another by evaluating chains forward alone.

## Proof sketch

Chain composition is additivity of the iteration count. Incomparability: if every digit of the message part of $m$ were at least that of $m'$, with one strict, the checksum of $m$ would be strictly smaller, so some checksum digit is smaller.

## Depends on

- [WOTS+ one-time signatures](wots-plus.md)

## Sources

- National Institute of Standards and Technology, "Stateless Hash-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.
