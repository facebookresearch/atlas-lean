# Boosting batch arguments from sublinear to polylogarithmic dependence on the batch size

There is an explicit polynomial $p$ such that the following holds. Assume a somewhere extractable hash family with succinct local openings (which exists, through rate-1 string oblivious transfer, under LWE, DDH, $O(1)$-LIN, QR or DCR). If there is an index BARG for batch circuit satisfiability whose proofs for $k$ instances with witnesses of length $m$ have size $\mathrm{poly}(m)\cdot L(k,\lambda)$, where $L(k,\lambda)\le k/p(\lambda)$ for all sufficiently large $k\ge\mathrm{poly}(\lambda)$ (for example $\mathrm{poly}(m,\lambda)\cdot k^{1-\epsilon}$ for a constant $\epsilon>0$), then there is an index BARG with proof size $\mathrm{poly}(\lambda,m,\log k)$, and SNARGs for deterministic time-$T$ and RAM computations with proof size $\mathrm{poly}(\lambda,\log T)$. Under the same hash assumption, BARGs with proof size $\mathrm{poly}(\lambda,m,\log k)$ exist iff flexible RAM SNARGs with partial input soundness and proof size $\mathrm{poly}(\lambda,\log T,\log N)$ exist. In particular such BARGs and SNARGs exist under the $O(1)$-LIN assumption on groups with a bilinear map, or under sub-exponential DDH together with QR.

## Proof sketch

First make the weak BARG somewhere extractable by committing to the witnesses with the somewhere extractable hash and proving openings (commit-and-prove). A somewhere extractable BARG gives a flexible RAM SNARG with partial input soundness whose succinctness inherits the BARG's, up to $\mathrm{poly}(\lambda,\log T)$ factors. A flexible RAM SNARG whose proof size is at most $T/\lambda$ for large $T$ gives a somewhere extractable BARG with polylogarithmic dependence on $k$, using a fully local somewhere extractable hash. Polylogarithmic BARGs then give SNARGs for P and for RAM computations by the delegation template.

## Depends on

- [Somewhere extractable (somewhere statistically binding) hash functions](somewhere-extractable-hash.md)
- [Non-interactive batch arguments for NP](batch-argument.md)

## Proof depends on

- [Delegation for deterministic computation from BARGs and somewhere extractable commitments](snarg-from-barg-and-hash.md)

## Sources

- Yael Tauman Kalai, Alex Lombardi, Vinod Vaikuntanathan, Daniel Wichs, "Boosting Batch Arguments and RAM Delegation", STOC (2023), Theorem 1.3, Theorems 8.1 and 8.3, Remark 8.1 and Corollary 8.2.
