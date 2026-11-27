# Farkas' lemma over linearly ordered fields

Let $K$ be a linearly ordered field, $A\in K^{p\times q}$ and $b\in K^p$. Exactly one of the following holds: (i) there is $x\in K^q$ with $Ax\le b$; (ii) there is $y\in K^p$ with $y\ge0$, $y^{T}A=0$ and $y^{T}b<0$. The proof needs no topology and holds, for example, over $\mathbb{Q}$.

## Proof sketch

Eliminate the variables one by one by Fourier–Motzkin elimination; each derived inequality is a nonnegative combination of the original rows. Either the final variable-free system is consistent, and back substitution produces $x$, or it contains $0\le c$ with $c<0$, whose combination coefficients give $y$.

## Proof depends on

- [Fourier–Motzkin elimination](../../../TheoryOfComputation/decision-procedures/satisfiability-modulo-theories/fouriermotzkin-elimination.md)

## Sources

- Alexander Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
- Jiří Matoušek, Bernd Gärtner, "Understanding and Using Linear Programming", Springer, 2007.
