# The Goldwasser–Micali scheme for $\ell$-bit messages

For a fixed modulus $N$ and a distribution of keys $(y, (p, q))$, the public-key scheme whose messages
are $\ell$-bit strings: encryption draws independent uniform units $x_1, \dots, x_\ell$ and outputs the
[bitwise encryption](encrypt-vec.md); decryption applies [trapdoor decryption](decrypt-bit.md) to each
component.

## Sources

- S. Goldwasser and S. Micali, "Probabilistic encryption & how to play mental poker keeping secret all partial information", Proc. 14th ACM STOC (1982), 365-377, Section 4.
