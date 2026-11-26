# Goyal-Harsha-Kumar-Shankar: near-linear time list decoding up to capacity

For every $\varepsilon > 0$ and $R \in (0,1)$ there are explicit univariate multiplicity codes and folded Reed-Solomon codes of rate $R$ with randomized list decoding algorithms correcting a $1 - R - \varepsilon$ fraction of errors in time $\tilde O(n)$ (for fixed $\varepsilon$), outputting a list of constant size.

## Proof sketch

The interpolation step is carried out with Alekhnovich's lattice-basis reduction over $\mathbb{F}[x]$ in quasi-linear time. The root-finding step requires solving, in quasi-linear time, linear differential equations $\tilde Q(x) + \sum_{i=0}^{m} Q_i(x) f^{(i)}(x) = 0$ (for multiplicity codes) or linear $\gamma$-difference equations (for FRS codes), done by divide and conquer on power series, followed by pruning to a constant-size list.

## Depends on

- [Folded Reed-Solomon codes](folded-reed-solomon-codes.md)
- [Univariate multiplicity codes](univariate-multiplicity-codes.md)

## Proof depends on

- [Guruswami-Wang: the list of folded RS and multiplicity codes lies in a low-dimensional subspace](linear-algebraic-list-decoding-into-a-subspace.md)
- [Kopparty-Ron-Zewi-Saraf-Wootters: constant list size up to capacity](constant-list-size-for-folded-reed-solomon-codes.md)

## Sources

- Rohan Goyal, Prahladh Harsha, Mrinal Kumar, Ashutosh Shankar, "Fast list-decoding of univariate multiplicity and folded Reed-Solomon codes", arXiv:2311.17841 (2023); ECCC TR23-185.
