# The Goldwasser–Micali scheme for one-bit messages

For a fixed modulus $N$ and a distribution of keys $(y, (p, q))$, the public-key encryption scheme
whose messages are bits: key generation samples a key from the distribution, the public key is $y$
and the secret key is $(p, q)$; encryption of $b$ samples a uniform unit $x$ modulo $N$ and outputs
the [encryption](encrypt-bit.md) of $b$ with randomness $x$; decryption is
[trapdoor decryption](decrypt-bit.md).

## Sources

- S. Goldwasser and S. Micali, "Probabilistic encryption & how to play mental poker keeping secret all partial information", Proc. 14th ACM STOC (1982), 365-377, Section 4.
- J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014, Definition 11.1 (the public-key schemes of the framework).
