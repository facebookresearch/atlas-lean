# Vanishing on a multiplicative subgroup and the quotient test

Let $H\le\mathbb{F}^{\times}$ have order $n$ and $Z_H(X)=X^{n}-1=\prod_{h\in H}(X-h)$. A polynomial $f\in\mathbb{F}[X]$ vanishes on $H$ iff $Z_H\mid f$. In a PIOP, the prover proves $f|_H=0$ for $\deg f\le D$ by sending $t=f/Z_H$ of degree $\le D-n$; the verifier checks $f(\zeta)=t(\zeta)Z_H(\zeta)$ at a uniformly random $\zeta\in\mathbb{F}$. If $Z_H\nmid f$ then for every polynomial $t$ of degree $\le D-n$, $\Pr_\zeta[f(\zeta)=t(\zeta)Z_H(\zeta)]\le D/|\mathbb{F}|$.

## Proof sketch

$H$ is the set of roots of $X^{n}-1$, which has $n$ distinct roots, so vanishing on $H$ is equivalent to divisibility. If $Z_H\nmid f$, then $f-tZ_H$ is a nonzero polynomial of degree at most $D$, which has at most $D$ roots.

## Depends on

- [PLONK gate equations with copy constraints](plonk-constraint-system.md)
- [Polynomial interactive oracle proofs](polynomial-iop.md)

## Sources

- Ariel Gabizon, Zachary J. Williamson, Oana Ciobotaru, "PLONK: Permutations over Lagrange-bases for Oecumenical Noninteractive arguments of Knowledge", IACR ePrint 2019/953 (2019).
