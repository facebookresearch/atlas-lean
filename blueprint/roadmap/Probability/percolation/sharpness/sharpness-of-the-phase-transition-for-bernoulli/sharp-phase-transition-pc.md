# Sharpness of the phase transition, stated with $p_c$

For Bernoulli bond percolation on $\mathbb{Z}^d$ with $d \ge 1$:

1. for every $p < p_c(d)$ there are $c, C > 0$ with $\mathbb{P}_p(0 \leftrightarrow \mathbb{Z}^d \setminus \Lambda_{n-1}) \le C e^{-cn}$ for all $n \in \mathbb{N}$;
2. for every $p$ with $p_c(d) < p < 1$, $\displaystyle \theta(p) \ge \frac{p - p_c(d)}{p(1 - p_c(d))}$.

The lecture notes state item 1 as $\mathbb{P}_p(0 \leftrightarrow \partial \Lambda_n) \le e^{-c_p n}$ for every $n \ge 1$; with the prefactor $C$ the statement above is weaker than that form. Item 2 is vacuous when $p_c = 1$, as for $d = 1$; for $d \ge 2$, [$p_c(d) < 1$](../../phase-transition/bounds-on-the-critical-probability/pc-lt-one-of-two-le-via-fk.md), so item 2 is informative there.

## Informally uses

- [Exponential decay of the one-arm probability below the threshold](cross-prob-exp-decay-of-mem-tilde-pc-set.md): Claim 1 of the source proof, exponential decay as soon as one finite $S \ni 0$ has $\varphi_p(S) < 1$.
- [Duminil-Copin–Tassion differential inequality](../duminil-copin-tassion-differential-inequality/dct-differential-inequality.md): Claim 2 of the source proof, $\theta_n' \ge \frac{1 - \theta_n}{p(1 - p)} \inf_S \varphi_p(S)$, integrated above $\tilde p_c$ to get the mean-field bound.
- [Russo's formula](../../../correlation-inequalities/harris-fkg-bk/russo-s-formula-and-pivotal-coordinates/deriv-prob-eq-sum-pivotal-prob.md): the source proves Claim 2 by Russo's formula (Proposition 2.7 of the lecture notes).
- [Van den Berg–Kesten inequality](../../../correlation-inequalities/harris-fkg-bk/van-den-berg-kesten-inequality/bk-inequality.md): the source proves Claim 1 by a BK-type decomposition, as in its Corollary 2.5.

## Background

- [The Duminil-Copin–Tassion quantity $\varphi_p(S)$](../the-duminil-copin-tassion-quantity-p-s-and-the-t/phi.md): the quantity whose monotonicity in $p$ turns the statement on $\tilde p_c$ into one on $p_c$.
- [Non-triviality of $p_c$ for $d \ge 2$](../../phase-transition/bounds-on-the-critical-probability/pc-lt-one-of-two-le-via-fk.md): $p_c(d) < 1$ for $d \ge 2$, which makes item 2 informative.
- [Kesten's theorem](../../phase-transition/critical-probability-of-the-square-lattice/pc-two-eq-half.md): on $\mathbb{Z}^2$, item 1 is the input that gives $p_c \le 1/2$.

## Sources

- Hugo Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes, IHÉS (version of 7 October 2018), Theorem 3.3 and its proof.
- Hugo Duminil-Copin and Vincent Tassion, *A new proof of the sharpness of the phase transition for Bernoulli percolation and the Ising model*, Comm. Math. Phys. 343 (2016), no. 2, 725–745, DOI 10.1007/s00220-015-2480-z; arXiv:1502.03050v3, Theorem 1.1 and §1.2.
