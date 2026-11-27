# Pre-matchings and Adachi's operator

In a one-to-one market with $n$ proposers and $n$ receivers and strict complete preferences, a **pre-matching** $\nu$ assigns to each proposer $p$ a tentative partner $\nu_P(p) \in \{\text{receivers}\} \cup \{\varnothing\}$ and to each receiver $r$ an independent tentative partner $\nu_R(r)$, with no consistency required. Order pre-matchings by: proposers weakly better and receivers weakly worse. **Adachi's operator** $T$ sends $\nu$ to the pre-matching in which each proposer gets its favourite receiver among those who prefer it to their $\nu_R$-partner, and each receiver gets its favourite proposer among those who prefer it to their $\nu_P$-partner. Pre-matchings form a complete lattice and $T$ is monotone.

## Depends on

- [Stable matching](../stable-marriage-problem/is-stable-matching.md)

## Sources

- H. Adachi, "On a Characterization of Stable Matchings", Economics Letters 68(1), 2000.
- J. Schummer and R. V. Vohra, "Mechanism Design without Money", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007.
