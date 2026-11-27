# GSW decryption has logarithmic-depth circuits

For GSW with parameters $(n, w)$ there is a Boolean circuit, generated in time polynomial in $n$ and $w$, that takes the serialized secret followed by a serialized ciphertext and outputs the decryption: it selects the designated row, computes its inner product with the secret digits modulo $2^w$ and outputs the exclusive-or of its two most significant bits (half-modulus decoding). The circuit has size polynomial in $n$ and $w$ and depth $O(\log n + \log w)$, and it is correct on every well-sized input pair, with no key-generation or noise hypothesis.

## Proof sketch

Use a balanced tree of carry-save adders for the inner product of $n+1$ residues of $w$ bits and a logarithmic-depth carry-lookahead adder for the final addition.

## Depends on

- [The Gentry–Sahai–Waters (GSW) encryption scheme](gsw-scheme.md)

## Sources

- Craig Gentry, Amit Sahai and Brent Waters, "Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based", Advances in Cryptology – CRYPTO 2013, 2013.
