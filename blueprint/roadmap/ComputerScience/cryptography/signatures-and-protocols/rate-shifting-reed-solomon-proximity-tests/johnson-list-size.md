# Johnson-bound list size for Reed–Solomon codes

Let $C=\mathrm{RS}[\mathbb{F},L,d]$ have rate $\rho=d/|L|$. For every $\eta\in(0,\sqrt{\rho})$ and every $f:L\to\mathbb{F}$, the number of codewords within relative distance $1-\sqrt{\rho}-\eta$ of $f$ is at most $1/(2\eta\sqrt{\rho})$. In particular, within the Johnson radius $1-\sqrt{\rho}$ the code is list-decodable with polynomial list size, and the Guruswami–Sudan algorithm finds the list in polynomial time.

## Proof sketch

This is the Johnson bound for codes of relative distance $1-\rho+1/|L|$: a second-moment (inclusion–exclusion) count over the agreement sets of the list members with $f$ bounds the list size in terms of the gap between the agreement $\sqrt{\rho}+\eta$ and the critical value $\sqrt{\rho}$. Guruswami–Sudan interpolates a bivariate polynomial with multiplicities and factors it.

## Depends on

- [Interactive oracle proofs of proximity for Reed–Solomon codes](rs-iopp.md)

## Proof depends on

- [Reed-Solomon codes are MDS](../../../../InformationTheory/error-correcting-codes/reed-solomon-codes/min-dist-code.md)

## Sources

- Venkatesan Guruswami, Madhu Sudan, "Improved Decoding of Reed-Solomon and Algebraic-Geometry Codes", IEEE Transactions on Information Theory (1999).
- Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, Shubhangi Saraf, "Proximity Gaps for Reed–Solomon Codes", FOCS (2020), IACR ePrint 2020/654.
- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "STIR: Reed–Solomon Proximity Testing with Fewer Queries", CRYPTO (2024), IACR ePrint 2024/390.
