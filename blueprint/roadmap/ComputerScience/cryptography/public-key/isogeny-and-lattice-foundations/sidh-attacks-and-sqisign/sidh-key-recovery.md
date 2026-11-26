# Polynomial-time key recovery attacks on SIDH

Given SIDH public data $(E_A,\varphi_A(P_B),\varphi_A(Q_B))$ with $3^{b}>2^{a}$, Alice's secret isogeny $\varphi_A$ can be recovered efficiently: (i) when $\mathrm{End}(E_0)$ contains a known small non-scalar endomorphism (as for the standard SIKE starting curves), in heuristic polynomial time by embedding $\varphi_A$ into a $(3^{b},3^{b})$-isogeny of abelian surfaces via Kani's lemma and testing digits of the secret (Castryck–Decru; Maino–Martindale–Panny–Pope–Wesolowski); and (ii) for an arbitrary starting curve, in polynomial time by embedding into an isogeny of abelian varieties of dimension $4$ or $8$ using Zarhin's trick (Robert). Consequently SIDH and SIKE are broken.

## Proof sketch

Write $3^{b}=2^{a}+c$ and find an auxiliary isogeny $\gamma$ of degree $c$ (from a known endomorphism of $E_0$ composed with small isogenies, or via a sum-of-squares decomposition in higher dimension). The diamond formed by $\varphi_A$ and $\gamma$ yields, by Kani's lemma, an $N$-isogeny with $N=3^{b}$ whose kernel is determined by the torsion point images; computing it with chains of $(3,3)$-isogenies reveals $\varphi_A$. Robert's version replaces the auxiliary isogeny by multiplication by integers on $E^{4}$ or $E^{8}$ via four-squares decompositions, needing no endomorphism knowledge.

## Depends on

- [The SIDH key exchange and its torsion point information](sidh-protocol.md)

## Proof depends on

- [Kani's lemma: isogeny diamonds give isogenies of abelian surfaces](kani-criterion.md)

## Sources

- Wouter Castryck, Thomas Decru, "An Efficient Key Recovery Attack on SIDH", EUROCRYPT (2023), IACR ePrint 2022/975.
- Luciano Maino, Chloe Martindale, Lorenz Panny, Giacomo Pope, Benjamin Wesolowski, "A Direct Key Recovery Attack on SIDH", EUROCRYPT (2023).
- Damien Robert, "Breaking SIDH in Polynomial Time", EUROCRYPT (2023), IACR ePrint 2022/1038.
