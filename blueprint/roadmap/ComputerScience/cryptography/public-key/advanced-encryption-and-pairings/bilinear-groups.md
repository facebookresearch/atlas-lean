# Bilinear groups

Let $\mathbb{G}$ and $\mathbb{G}_T$ be cyclic groups of the same prime order $p$, written multiplicatively. A *symmetric bilinear pairing* is a map $e : \mathbb{G} \times \mathbb{G} \to \mathbb{G}_T$ that is

- *bilinear*: $e(g^a, h^b) = e(g, h)^{ab}$ for all $g, h \in \mathbb{G}$ and $a, b \in \mathbb{Z}_p$;
- *non-degenerate*: $e$ does not send every pair to the identity of $\mathbb{G}_T$, so that $e(g, g)$ generates $\mathbb{G}_T$ whenever $g$ generates $\mathbb{G}$; and
- *efficiently computable*.

A pairing with these three properties is *admissible*, and $(\mathbb{G}, \mathbb{G}_T, e)$ is a *symmetric bilinear group*. In the asymmetric variants the first argument ranges over a group $\mathbb{G}$ and the second over a second group $\hat{\mathbb{G}}$ of order $p$, with the same bilinearity and non-degeneracy conditions.

## Sources

- D. Boneh and M. Franklin, "Identity-based encryption from the Weil pairing", *SIAM Journal on Computing* 32(3):586–615, 2003, Section 3.1 (admissible bilinear maps, written additively in the first group)
- A. Kate, G. M. Zaverucha and I. Goldberg, "Constant-size commitments to polynomials and their applications", technical report CACR 2010-10, <https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf>, Appendix A
