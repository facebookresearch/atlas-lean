# Length-prepended CBC-MAC is a variable-length PRF and MAC

If $F$ is a PRF on $n$-bit blocks with $2^{-n}$ negligible, then length-prepended CBC-MAC on messages of $0$ to $L(n)$ whole blocks is a PRF against arbitrary adversaries and a strongly unforgeable MAC.

## Proof sketch

Prepending the block count is a prefix-free encoding, so security follows from the prefix-free security of raw CBC-MAC; a PRF with super-polynomial output space is a secure MAC.

## Depends on

- [CBC-MAC](cbc-mac.md)

## Proof depends on

- [CBC-MAC is a prefix-free PRF](cbc-mac-is-a-prefix-free-prf.md)
- [A prefix-free PRF composed with a prefix-free encoding is a variable-length PRF](../pseudorandom-function-constructions/prefix-free-prf-with-prefix-free-encoding.md)
- [The MAC from a PRF, concrete security](../pseudorandom-functions/mac-game-le.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare, J. Kilian and P. Rogaway, "The Security of the Cipher Block Chaining Message Authentication Code", Journal of Computer and System Sciences 61(3), 2000.
