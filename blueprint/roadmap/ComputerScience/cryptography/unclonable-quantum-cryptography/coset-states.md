# Coset states

For a subspace $A\subseteq\mathbb{F}_2^{n}$ of dimension $n/2$ and vectors $s,s'\in\mathbb{F}_2^{n}$, the *coset state* is

$$
|A_{s,s'}\rangle=\frac{1}{\sqrt{|A|}}\sum_{a\in A}(-1)^{\langle s',a\rangle}|a+s\rangle.
$$

Measuring it in the computational basis yields a uniformly random element of $A+s$, and measuring after $H^{\otimes n}$ yields a uniformly random element of $A^{\perp}+s'$. Coset states generalize subspace states ($s=s'=0$) and serve as the main building block of unclonable cryptography in the plain model.

## Depends on

- [Query lower bound for duplicating subspace states](subspace-state-unclonability.md)

## Sources

- Andrea Coladangelo, Jiahui Liu, Qipeng Liu, Mark Zhandry, "Hidden Cosets and Applications to Unclonable Cryptography", CRYPTO (2021), IACR ePrint 2021/946.
