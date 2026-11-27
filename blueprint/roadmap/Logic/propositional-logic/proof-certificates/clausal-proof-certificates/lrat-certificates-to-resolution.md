# Accepted LRAT certificates translate into resolution refutations

Let $\varphi$ be a CNF formula with $|\varphi|$ clauses and $N$ variables, and let $\pi$ be an LRAT certificate consisting of RUP addition steps (with hints) and deletions, accepted by the LRAT checker. Then $\varphi$ has a resolution refutation with at most $|\varphi| + \min(H, S \cdot N)$ lines, where $H$ is the total number of hints of $\pi$ and $S$ its number of steps. Conversely, every tree-like resolution refutation with $s$ nodes compiles into an accepted LRAT certificate with one RUP step per resolution step, each hinting its two premises.

## Proof sketch

Each RUP step with hints $h_1,\dots,h_k$ is a trivial resolution chain of at most $\min(k, N)$ resolutions, since each step resolves away a distinct variable; concatenating the chains gives the refutation. Conversely a resolvent is a RUP clause of its premises.

## Depends on

- [Trivial resolution derivations](trivial-resolution-derivations.md)
- [Accepted LRAT proofs refute CNF formulas](../accepted-lrat-proofs-refute-cnf-formulas.md)
- [Resolution refutation](../../resolution-size-and-width/is-resolution-refutation.md)

## Sources

- P. Beame, H. Kautz and A. Sabharwal, "Towards Understanding and Harnessing the Potential of Clause Learning", Journal of Artificial Intelligence Research 22, 319–351, 2004.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction — CADE 26, LNCS 10395, 2017.
