# Regev's public-key encryption from learning with errors

In Regev's scheme the public key is $(A, b = As + e) \in \mathbb{Z}_q^{m \times n} \times \mathbb{Z}_q^m$ for a secret $s$ and error $e$ from the LWE distribution; a bit $\mu$ is encrypted by choosing a uniform $r \in \{0,1\}^m$ and outputting $(r^{\mathsf T}A,\ r^{\mathsf T}b + \mu\lfloor q/2 \rfloor)$, and a ciphertext $(u, v)$ decrypts to $0$ if $v - u s$ is closer to $0$ than to $\lfloor q/2 \rfloor$ modulo $q$. Decryption is correct whenever $|r^{\mathsf T}e| < \lfloor q/2 \rfloor / 2$, where $r^{\mathsf T}e$ is taken as an integer of absolute value at most $q/2$. The scheme is CPA secure if decision LWE holds for the public-key distribution and $m \ge (n+1)\log_2 q + \omega(\log n)$: under decision LWE the public key may be replaced by a uniform matrix, and then the leftover hash lemma, applied to the universal family $r \mapsto [A \mid b]^{\mathsf T} r$, makes the ciphertext statistically close to uniform. Regev's parameter setting achieves both: $q$ a prime between $n^2$ and $2n^2$, $m = (1 + \varepsilon)(n + 1)\log q$ for a constant $\varepsilon > 0$, and the discretized Gaussian error $\bar\Psi_\alpha$ with $\alpha = o(1/(\sqrt n \log n))$.

## Depends on

- [Learning with errors](learning-with-errors.md)
- [Public-key encryption scheme](../../security-games/generic-security-games/pkescheme.md)

## Expansion

This page becomes ready once:

- The bound m ≥ (n+1) log₂ q + ω(log n) used with the leftover hash lemma must be matched to a cited proof; Regev uses the parameter setting stated

## Sources

- O. Regev, "On lattices, learning with errors, random linear codes, and cryptography", *Journal of the ACM* 56(6), Article 34, 2009; <https://arxiv.org/abs/2401.03703>
- C. Peikert, "A decade of lattice cryptography", *Foundations and Trends in Theoretical Computer Science* 10(4):283–424, 2016; ePrint 2015/939, <https://eprint.iacr.org/2015/939>
