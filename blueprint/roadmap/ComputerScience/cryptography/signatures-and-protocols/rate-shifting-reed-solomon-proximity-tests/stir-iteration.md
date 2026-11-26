# One STIR iteration: fold, shift to a smaller domain, quotient

Let $f$ be claimed in $\mathrm{RS}[\mathbb{F},L,d]$ of rate $\rho$. One STIR iteration with folding parameter $k$ consists of: the verifier sends $\alpha$; the prover sends an oracle $g$ claimed to be the evaluation of $\mathrm{Fold}(\hat{f},\alpha)$ on a new domain $L'$ with $|L'|=|L|/2$ (disjoint from $L^{k}$); an out-of-domain sample is answered; the verifier makes $t$ queries to $f$ at random points of $L^{k}$ (each requiring $k$ reads of $f$) to obtain values $\mathrm{Fold}(f,\alpha)(y)$; and the next function is $f'=\mathrm{Quot}(g,S,\mathrm{Ans})$ (degree-corrected), where $S$ collects the out-of-domain and queried points. The new code has degree $d/k$ and rate $\rho'=\rho\cdot 2/k$. Write $\mathrm{err}^{\star}(d^{\circ},\rho^{\circ},\delta^{\circ},m)$ for the error of the Ben-Sasson–Carmon–Ishai–Kopparty–Saraf correlated-agreement theorem for $m$ functions combined along a degree-$(m-1)$ curve, relative to $\mathrm{RS}$ codes of degree $d^{\circ}$ and rate $\rho^{\circ}$ at distance $\delta^{\circ}$. Suppose $f$ is $\delta$-far from $\mathrm{RS}[\mathbb{F},L,d]$ with $\delta<1-\sqrt{\rho}$, and let $\delta'<\min\{1-\rho'-1/|L'|,\,1-\sqrt{\rho'}\}$ be such that $\mathrm{RS}[\mathbb{F},L',d/k]$ is $(\delta',\ell)$-list decodable. Then the iteration is round-by-round sound with errors at most $\mathrm{err}^{\star}(d/k,\rho,\delta,k)$ for the folding round, $\binom{\ell}{2}\frac{d/k}{|\mathbb{F}|-|L'|}$ for the out-of-domain round, and $(1-\delta)^{t}+\mathrm{err}^{\star}(d/k,\rho',\delta',t+1)$ for the query round, the last term accounting for the degree correction of $f'$ (Lemma 5.4 of the source, with one out-of-domain sample).

## Proof sketch

If $g$ is close to the evaluation of a polynomial inconsistent with $\mathrm{Fold}(f,\alpha)$ at a queried point, quotienting turns that inconsistency into distance from the new code (quotient lemma). If $g$ is consistent at all queried points while $\mathrm{Fold}(f,\alpha)$ is far from the code, each query catches the discrepancy with probability at least $\delta$. Out-of-domain sampling reduces the list to one candidate.

## Depends on

- [k-wise folding of Reed–Solomon codewords reduces degree](rs-folding-operator.md)
- [Quotienting by answered evaluation claims preserves distance](quotient-distance-preservation.md)
- [Interactive oracle proofs of proximity for Reed–Solomon codes](rs-iopp.md)

## Proof depends on

- [Out-of-domain sampling pins down a unique list-decoded codeword](out-of-domain-sampling.md)

## Sources

- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "STIR: Reed–Solomon Proximity Testing with Fewer Queries", CRYPTO (2024), IACR ePrint 2024/390.
