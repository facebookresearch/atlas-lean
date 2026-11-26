# Generic Reed-Solomon codes are MDS(l) for every l

For all $\ell \ge 2$ and $1 \le k \le n$, generic Reed-Solomon codes $\mathrm{RS}_k(\alpha)$ are $\mathrm{MDS}(\ell)$.

## Proof sketch

The dimension of $G_{A_1} \cap \cdots \cap G_{A_\ell}$ is governed by the rank of a block matrix whose blocks are column restrictions of $G$; computing a generic rank amounts to finding a zero pattern attaining it. Brakensiek, Gopi and Makam show the relevant intersections can be realized through generator matrices with prescribed zero patterns satisfying the GM-MDS condition, so by the GM-MDS theorem generic RS generator matrices achieve the same ranks as a generic matrix.

## Depends on

- [Higher order MDS codes MDS(l)](higher-order-mds-codes.md)
- [Generic and randomly punctured Reed-Solomon codes](generic-reed-solomon-codes.md)

## Proof depends on

- [GM-MDS theorem (Lovett; Yildiz-Hassibi)](gm-mds-theorem.md)

## Sources

- Joshua Brakensiek, Sivakanth Gopi, Visu Makam, "Generic Reed-Solomon codes achieve list-decoding capacity", STOC (2023), SIAM Journal on Computing (2024); arXiv:2206.05256.
