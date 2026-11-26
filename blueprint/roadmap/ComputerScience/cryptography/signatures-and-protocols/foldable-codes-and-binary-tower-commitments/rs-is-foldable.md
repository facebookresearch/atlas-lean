# Reed–Solomon codes on smooth multiplicative domains are foldable

Let $\omega$ be a primitive $n_{i+1}$-th root of unity with $n_{i+1}=2n_i$, and let $C_i=\mathrm{RS}[\mathbb{F},\langle\omega^{2}\rangle,k_i]$ with evaluation points ordered as $\omega^{2j}$. Writing a polynomial of degree $< k_{i+1}$ as $\hat{m}(X)=\hat{m}_0(X^{2})+X\hat{m}_1(X^{2})$ (an ordering of message coefficients), its evaluations at $\omega^{j}$ and $\omega^{j+n_i}=-\omega^{j}$ are $\hat{m}_0(\omega^{2j})\pm\omega^{j}\hat{m}_1(\omega^{2j})$. Hence the Reed–Solomon family is foldable with $T_i=\mathrm{diag}(\omega^{j})_{j< n_i}$ and $T'_i=-T_i$, and $T_i-T'_i=2T_i$ is invertible in odd characteristic.

## Proof sketch

This is the radix-2 FFT butterfly: even and odd parts of $\hat{m}$ evaluated on the squared domain combine with $\pm\omega^{j}$. Matching the block form of the foldable generator gives the diagonal matrices.

## Depends on

- [Foldable linear codes](foldable-linear-code.md)
- [Interactive oracle proofs of proximity for Reed–Solomon codes](../rate-shifting-reed-solomon-proximity-tests/rs-iopp.md)

## Proof depends on

- [k-wise folding of Reed–Solomon codewords reduces degree](../rate-shifting-reed-solomon-proximity-tests/rs-folding-operator.md)

## Sources

- Hadas Zeilberger, Binyi Chen, Ben Fisch, "BaseFold: Efficient Field-Agnostic Polynomial Commitment Schemes from Foldable Codes", CRYPTO (2024), IACR ePrint 2023/1705.
- Eli Ben-Sasson, Iddo Bentov, Yinon Horesh, Michael Riabzev, "Fast Reed-Solomon Interactive Oracle Proofs of Proximity", ICALP (2018).
