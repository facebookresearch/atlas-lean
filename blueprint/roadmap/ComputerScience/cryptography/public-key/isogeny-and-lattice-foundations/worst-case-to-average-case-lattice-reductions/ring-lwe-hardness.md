# Hardness of Ring-LWE from worst-case problems on ideal lattices

Let $K=\mathbb{Q}(\zeta_m)$ be a cyclotomic number field with ring of integers $R$, $q\equiv 1\pmod m$ a prime of polynomial size, and $\alpha q\ge\omega(\sqrt{\log n})$ with $n=\varphi(m)$. Then: (i) there is a quantum polynomial-time reduction from approximate $\mathrm{SIVP}$ on ideal lattices of $K$ with factor $\mathrm{poly}(n)/\alpha$ to search Ring-LWE over $R_q$ with suitable (elliptic) Gaussian error; and (ii) search Ring-LWE reduces classically to decision Ring-LWE with spherical-like error distributions, using the splitting of $q$ into $n$ prime ideals and the transitive action of the Galois group on them.

## Proof sketch

Adapt Regev's iterative reduction to ideal lattices using the canonical embedding and the fact that ideals of $R$ are modules over $R$, so samples from discrete Gaussians on an ideal translate to Ring-LWE samples. For search-to-decision, guess the secret modulo one prime ideal $\mathfrak{q}_i$ at a time by testing hybrid distributions; Galois automorphisms move any prime ideal to any other, so decision hardness for one ideal suffices.

## Depends on

- [Approximate lattice problems GapSVP and SIVP](gapsvp-and-sivp.md)

## Proof depends on

- [Regev's quantum worst-case to average-case reduction for LWE](regev-worst-case-reduction.md)

## Sources

- Vadim Lyubashevsky, Chris Peikert, Oded Regev, "On Ideal Lattices and Learning with Errors over Rings", EUROCRYPT (2010); JACM (2013).
