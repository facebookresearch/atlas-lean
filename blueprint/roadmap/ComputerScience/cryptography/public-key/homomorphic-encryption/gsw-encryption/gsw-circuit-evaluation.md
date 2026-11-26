# GSW evaluates Boolean circuits of bounded depth

Compile a Boolean circuit into consecutive NAND layers. For GSW parameters whose fresh ciphertexts have error bounded by $B$ (for LWE errors bounded by $\beta$ in absolute value, $B = m\beta$), each NAND gate multiplies the error bound by at most $N+1$, and every compiled circuit of NAND depth $L$ with $q/B > 8(N+1)^L$ is evaluated correctly on fresh encryptions, constants being encrypted noiselessly and copies forwarded (Gentry, Sahai and Waters, Sections 3.3 and 3.4). In particular, for $B$ not too large, a modulus with $\log_2 q = O(L \log N)$ suffices, so for circuits of NAND depth $O(\log n)$ the ratio $q/B$ can be taken quasi-polynomial in $n$.

## Proof sketch

By the noise lemma the error after $L$ NAND layers is at most $(N+1)^L B$, which is below $q/8$ when $q/B > 8(N+1)^L$; an error below $q/8$ leaves the decryption margin.

## Depends on

- [The Gentry–Sahai–Waters (GSW) encryption scheme](gsw-scheme.md)

## Proof depends on

- [Noise growth of GSW encryption and NAND](gsw-noise-growth.md)
- [Correct decryption of GSW ciphertexts with small noise](gsw-decryption-correctness.md)

## Sources

- Craig Gentry, Amit Sahai and Brent Waters, "Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based", Advances in Cryptology – CRYPTO 2013, 2013.
