# Hellinger distance controls differences of mean rewards

Let $P, Q$ be distributions of a reward $r \in [0,1]$ (with arbitrary observations) and $D_H^2(P, Q) = \int (\sqrt{dP} - \sqrt{dQ})^2$. Then

$$
\big|\mathbb{E}_P[r] - \mathbb{E}_Q[r]\big| \le d_{\mathrm{TV}}(P, Q) \le D_H(P, Q).
$$

In particular, for models $M, M'$ and a decision $\pi$, $|f^M(\pi) - f^{M'}(\pi)| \le D_H(M(\pi), M'(\pi))$, which is the inequality used to compare regret on alternative models with estimation error in the DEC.

## Proof sketch

The first inequality holds because $r$ takes values in $[0,1]$. For the second, $2 d_{\mathrm{TV}} = \int|p - q| = \int|\sqrt p - \sqrt q|(\sqrt p + \sqrt q) \le \big(\int(\sqrt p - \sqrt q)^2\big)^{1/2}\big(\int(\sqrt p + \sqrt q)^2\big)^{1/2}$ by Cauchy–Schwarz, and $\int(\sqrt p + \sqrt q)^2 \le 4$.

## Depends on

- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)
- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)
- [Decision making with structured observations](decision-making-structured-observations.md)

## Sources

- D. J. Foster, A. Rakhlin, "Foundations of Reinforcement Learning and Interactive Decision Making", lecture notes, revised edition (September 2026), arXiv:2312.16730v2, Section 7.2 (Lemma 7.1 and Eq. (7.9)).
- A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer (2009), Section 2.4.
