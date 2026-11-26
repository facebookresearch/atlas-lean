# Noise growth of GSW encryption and NAND

Say a GSW ciphertext $C$ encrypts $\mu$ with integer error $\varepsilon \in \mathbb{Z}^N$ if $C G^{\mathsf T} s \equiv \mu G^{\mathsf T} s + \varepsilon \pmod q$. (i) A fresh encryption has error $R e$, so if every LWE error has $|e_i| \le \beta$ then $\|\varepsilon\|_\infty \le m\beta$. (ii) If $C_1, C_2$ encrypt $\mu_1, \mu_2$ with errors bounded by $B_1, B_2$, then their NAND encrypts $1 - \mu_1\mu_2$ with error $-(C_1 \varepsilon_2 + \mu_2 \varepsilon_1)$, of size at most $N B_2 + B_1$. (iii) Noiseless constants have error $0$. Consequently a NAND circuit of depth $L$ on fresh inputs produces errors at most $(N + 1)^L m \beta$.

## Proof sketch

Use $C_1 C_2 G^{\mathsf T} s = C_1(\mu_2 G^{\mathsf T} s + \varepsilon_2) = \mu_1\mu_2 G^{\mathsf T}s + \mu_2\varepsilon_1 + C_1\varepsilon_2$; $C_1$ is a binary matrix, so $C_1\varepsilon_2$ is a vector of subset sums of entries of $\varepsilon_2$.

## Depends on

- [The Gentry–Sahai–Waters (GSW) encryption scheme](gsw-scheme.md)

## Sources

- Craig Gentry, Amit Sahai and Brent Waters, "Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based", Advances in Cryptology – CRYPTO 2013, 2013.
