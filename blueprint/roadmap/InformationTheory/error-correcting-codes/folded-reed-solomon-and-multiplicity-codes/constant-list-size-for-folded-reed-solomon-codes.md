# Kopparty-Ron-Zewi-Saraf-Wootters: constant list size up to capacity

For every $\varepsilon > 0$ and $R \in (0,1)$, folded Reed-Solomon codes and univariate multiplicity codes of rate $R$ with folding parameter $s = \mathrm{poly}(1/\varepsilon)$ are $\big(1 - R - \varepsilon, (1/\varepsilon)^{O(\varepsilon^{-1}\log(1/R))}\big)$-list decodable, with a randomized polynomial-time list decoding algorithm whose running time is $\mathrm{poly}(n)$ for fixed $\varepsilon$; folded Reed-Solomon codes are moreover $\big(1 - R - \varepsilon, \ell, (\ell/\varepsilon)^{O(\varepsilon^{-1}\log(\ell/R))}\big)$-list recoverable.

## Proof sketch

Starting from the Guruswami-Wang affine subspace of dimension $m - 1$, show that it contains only a constant number of codewords close to the received word: randomly restrict to a few coordinates where the received word agrees with the target codeword and use that FRS codes behave like subspace designs on such restrictions, so each restriction cuts the candidate subspace's dimension. An iterative pruning yields list size depending only on $\varepsilon$.

## Depends on

- [List recovery and relaxed generalized Singleton bounds](list-recovery-of-folded-codes.md)
- [Folded Reed-Solomon codes](folded-reed-solomon-codes.md)
- [Univariate multiplicity codes](univariate-multiplicity-codes.md)

## Proof depends on

- [Guruswami-Wang: the list of folded RS and multiplicity codes lies in a low-dimensional subspace](linear-algebraic-list-decoding-into-a-subspace.md)

## Sources

- Swastik Kopparty, Noga Ron-Zewi, Shubhangi Saraf, Mary Wootters, "Improved list decoding of folded Reed-Solomon and multiplicity codes", FOCS (2018), SIAM Journal on Computing 52(3) (2023); arXiv:1805.01498.
- Itzhak Tamo, "Tighter list-size bounds for list-decoding and recovery of folded Reed-Solomon and multiplicity codes", IEEE Transactions on Information Theory (2024); arXiv:2312.17097.
