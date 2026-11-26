# One STIR iteration: fold, shift to a smaller domain, quotient

Let $f$ be claimed in $\mathrm{RS}[\mathbb{F},L,d]$ of rate $\rho$. One STIR iteration with folding parameter $k$ consists of: the verifier sends $\alpha$; the prover sends an oracle $g$ claimed to be the evaluation of $\mathrm{Fold}(\hat{f},\alpha)$ on a new domain $L'$ with $|L'|=|L|/2$ (disjoint from $L^{k}$); an out-of-domain sample is answered; the verifier makes $t$ queries to $f$ at random points of $L^{k}$ (each requiring $k$ reads of $f$) to obtain values $\mathrm{Fold}(f,\alpha)(y)$; and the next function is $f'=\mathrm{Quot}(g,S,\mathrm{Ans})$ (degree-corrected), where $S$ collects the out-of-domain and queried points. The new code has degree $d/k$ and rate $\rho'=\rho\cdot 2/k$. If $f$ is $\delta$-far, then except with probability roughly $(1-\delta)^{t}$ plus list-decoding and proximity-gap errors, $f'$ is $\delta'$-far from the new code.

## Proof sketch

If $g$ is close to the evaluation of a polynomial inconsistent with $\mathrm{Fold}(f,\alpha)$ at a queried point, quotienting turns that inconsistency into distance from the new code (quotient lemma). If $g$ is consistent at all queried points while $\mathrm{Fold}(f,\alpha)$ is far from the code, each query catches the discrepancy with probability at least $\delta$. Out-of-domain sampling reduces the list to one candidate.

## Depends on

- [k-wise folding of Reed–Solomon codewords reduces degree](rs-folding-operator.md)
- [Quotienting by answered evaluation claims preserves distance](quotient-distance-preservation.md)
- [Out-of-domain sampling pins down a unique list-decoded codeword](out-of-domain-sampling.md)

## Proof depends on

- [Quotienting by answered evaluation claims preserves distance](quotient-distance-preservation.md)
- [Out-of-domain sampling pins down a unique list-decoded codeword](out-of-domain-sampling.md)
- [k-wise folding of Reed–Solomon codewords reduces degree](rs-folding-operator.md)

## Sources

- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "STIR: Reed–Solomon Proximity Testing with Fewer Queries", CRYPTO (2024), IACR ePrint 2024/390.
