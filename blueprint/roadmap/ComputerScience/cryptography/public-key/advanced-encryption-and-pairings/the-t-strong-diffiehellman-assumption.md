# Pairing-based assumptions: BDH and t-SDH

Let $(\mathbb{G}, \mathbb{G}_T, e)$ be a symmetric bilinear group of prime order $p$ with generator $g$. Each assumption asserts that every efficient algorithm solves the stated problem with negligible probability.

- **Bilinear Diffie–Hellman (BDH):** given $(g, g^a, g^b, g^c)$ for uniform $a, b, c \in \mathbb{Z}_p^*$, compute $e(g, g)^{abc}$.
- **$t$-strong Diffie–Hellman ($t$-SDH)**, for $t \ge 1$: given $(g, g^\alpha, g^{\alpha^2}, \dots, g^{\alpha^t})$ for uniform $\alpha \in \mathbb{Z}_p^*$, output a pair $(c, g^{1/(\alpha + c)})$ with $c \in \mathbb{Z}_p \setminus \{-\alpha\}$.

## Depends on

- [Bilinear groups](bilinear-groups.md)
- [Winning probability of a game](../../security-games/games-and-advantages/win-prob.md)

## Sources

- A. Kate, G. M. Zaverucha and I. Goldberg, "Constant-size commitments to polynomials and their applications", *ASIACRYPT 2010*, LNCS 6477, Springer, 2010; technical report CACR 2010-10, <https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf>, Definition 2.3
- D. Boneh and M. Franklin, "Identity-based encryption from the Weil pairing", *SIAM Journal on Computing* 32(3):586–615, 2003, Section 3.1 (the BDH problem)
- Original assumption: D. Boneh and X. Boyen, "Short signatures without random oracles", *EUROCRYPT 2004*, LNCS 3027, Springer, 2004. The $t$-SDH statement above follows Kate, Zaverucha and Goldberg, Definition 2.3, who credit it to Boneh and Boyen.
