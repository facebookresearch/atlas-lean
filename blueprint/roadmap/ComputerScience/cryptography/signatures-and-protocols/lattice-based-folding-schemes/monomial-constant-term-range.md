# Constant-term extraction of exponents in the negacyclic ring

Let $d$ be a power of two, $d'=d/2$, $\mathcal{R}_q=\mathbb{Z}_q[X]/(X^{d}+1)$, and let $\mathcal{M}=\{0,1,X,\dots,X^{d-1}\}\subseteq\mathcal{R}_q$ be the monomials with coefficient one together with $0$. For an integer $a\in(-d,d)$ set $\exp(a)=\mathrm{sgn}(a)X^{a}$, which lies in $\mathcal{M}$ (for $a<0$, $-X^{a}=X^{a+d}$), and let $\mathrm{EXP}(a)=\{\exp(a)\}$ for $a\ne0$ and $\mathrm{EXP}(0)=\{0,1,X^{d'}\}$. Define

$$
\psi=\sum_{1\le i<d'}i\cdot\bigl(X^{-i}+X^{i}\bigr)\in\mathcal{R}_q .
$$

For every $a\in\mathbb{Z}_q$: if $a\in(-d',d')$, then $\mathrm{ct}(b\cdot\psi)=a$ for every $b\in\mathrm{EXP}(a)$; conversely, if some $b\in\mathcal{M}$ satisfies $\mathrm{ct}(b\cdot\psi)=a$, then $a\in(-d',d')$ and $b\in\mathrm{EXP}(a)$. Hence a range claim $a\in(-d',d')$ is certified by exhibiting $b$ with both $b\in\mathcal{M}$ and $\mathrm{ct}(b\psi)=a$; monomiality of a committed $b$ alone says nothing about a separately claimed $a$.

## Proof sketch

Multiplying by $b\in\mathcal{M}\setminus\{0\}$ rotates the coefficients of $\psi$ and flips the signs of those that wrap around, so $\mathrm{ct}(b\psi)$ is, up to sign, one coefficient of $\psi$ and lies in $(-d',d')$; for $b=0$ it is $0$. For $a\ne0$ in that range, the only monomial term of $\psi$ that $\exp(a)$ moves to the constant position contributes exactly $a$. The constant term vanishes exactly for $b=0$, $b=1$ and $b=X^{d'}$, which gives $\mathrm{EXP}(0)$, and inspecting which rotation produces each nonzero value gives $b=\exp(a)$.

## Depends on

- [Strong sampling sets of short challenges in power-of-two cyclotomic rings](short-challenge-sets.md)

## Sources

- Dan Boneh, Binyi Chen, "LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding for Succinct Proof Systems", CRYPTO (2025), IACR ePrint 2025/247, Section 2 (Lemma 2.2 and the definitions of $\mathcal{M}$, $\exp$ and $\mathrm{EXP}$).
