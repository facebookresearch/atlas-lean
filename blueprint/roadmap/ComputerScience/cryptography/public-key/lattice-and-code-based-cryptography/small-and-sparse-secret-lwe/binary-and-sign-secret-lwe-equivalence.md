# Binary and sign secrets give equivalent LWE problems for odd moduli

For odd $q$, the maps $(A,b)\mapsto(A/2,\,b-(A/2)u)$ and $(A,b)\mapsto(2A,\,b+Au)$ with $u=(1,\dots,1)$ turn binary-secret LWE samples into $\pm1$-secret samples and back, and uniform samples into uniform samples, preserving the error and the number of samples.

Let $q\ge3$ be an odd integer, $n,m\ge1$, $\chi$ any error distribution on $\mathbb{Z}_q$, and $u=(1,\dots,1)\in\mathbb{Z}_q^n$. Let $\mathrm{LWE}_{0,1}$ and $\mathrm{LWE}_{\pm}$ denote LWE with $m$ samples, modulus $q$, error $\chi^m$ and secret uniform on $\{0,1\}^n$, respectively $\{-1,1\}^n$ (taken modulo $q$).

1. The map $\varphi(A,b)=(A/2,\;b-(A/2)u)$, with $A/2=2^{-1}A$ computed modulo $q$, sends $\mathrm{LWE}_{0,1}$ to $\mathrm{LWE}_{\pm}$ and the uniform distribution on $\mathbb{Z}_q^{m\times n}\times\mathbb{Z}_q^m$ to itself; the new secret is $2s-u$.
2. The map $\psi(A,b)=(2A,\;b+Au)$ sends $\mathrm{LWE}_{\pm}$ to $\mathrm{LWE}_{0,1}$ and uniform to uniform; the new secret is $(s+u)/2$.

Consequently a distinguisher for one problem composed with the corresponding map is a distinguisher for the other with exactly the same advantage. The reductions are polynomial time and preserve the modulus, the dimension, the number of samples and the error distribution.

## Expansion

Since $q$ is odd, $2$ is invertible modulo $q$, so $A\mapsto A/2$ and $A\mapsto 2A$ are bijections of $\mathbb{Z}_q^{m\times n}$ preserving the uniform law. If $b=As+e$ with $s\in\{0,1\}^n$, then $b-(A/2)u=(A/2)(2s-u)+e$ and $2s-u$ is uniform on $\{-1,1\}^n$. If $b=As'+e$ with $s'\in\{\pm1\}^n$, then $b+Au=(2A)\bigl((s'+u)/2\bigr)+e$ with $(s'+u)/2$ uniform on $\{0,1\}^n$. If $b$ is uniform and independent of $A$, so is $b$ minus any function of $A$. The same maps translate a search solution for one problem into one for the other.

## Depends on

- [LWE with a prescribed secret distribution](lwe-with-a-secret-distribution.md)
- [Distinguishing advantage](../../../security-games/games-and-advantages/advantage.md)

## Proof depends on

None.

## Sources

- Daniele Micciancio, "On the Hardness of Learning With Errors with Binary Secrets", Theory of Computing 14(13):1–17, 2018, https://doi.org/10.4086/toc.2018.v014a013, Lemmas 2.12 and 2.13 and the remark preceding them.
