# GSW evaluates Boolean circuits of bounded depth

Compile a Boolean circuit into consecutive NAND layers. For GSW parameters with fresh noise bound $m\beta$, every compiled circuit of NAND depth $L$ with $4 (N+1)^L m\beta < q$ is evaluated correctly on fresh encryptions, constants being encrypted noiselessly and copies forwarded. In particular, with $t = 1 + \lceil \log_2(\lambda + 2) \rceil$, digit width $w = 16384\, t^2$, $N = (n+1)w$, $m = N + 2\lambda$ and depth budget $L = 512\, t$, the modulus $q = 2^w$ leaves a noise margin for every circuit of logarithmic NAND depth at most $L$.

## Proof sketch

By the noise lemma the error after $L$ NAND layers is at most $(N+1)^L m\beta$; since $\log_2((N+1)^L m\beta) = O(L \log N) = O(t^2) < w$ for the chosen constants, the decryption margin holds.

## Depends on

- [The Gentry–Sahai–Waters (GSW) encryption scheme](gsw-scheme.md)

## Proof depends on

- [Noise growth of GSW encryption and NAND](gsw-noise-growth.md)
- [Correct decryption of GSW ciphertexts with small noise](gsw-decryption-correctness.md)

## Sources

- Craig Gentry, Amit Sahai and Brent Waters, "Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based", Advances in Cryptology – CRYPTO 2013, 2013.
