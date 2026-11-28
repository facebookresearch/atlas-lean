# Bit composition, CRT reconstruction and constant division gadgets for arithmetic garbling

For a prime $p$ and $k \ge 1$: (i) over $\mathbb{Z}/p^k$, *bit composition* $\mathrm{bitComp}$ inverts bit decomposition, writing $x$ as $k$ base-$p$ digits of $\lceil \log_2 p \rceil$ bits each; a garbled linear-composition table that holds the labels of bits $z_i$ with colours and pads lets the evaluator obtain the affine label of $\sum_i c_i z_i$, and if the key shares form a uniform additive sharing of the output key, the active rows are perfectly private; (ii) *CRT reconstruction*: for pairwise coprime moduli $m_1, \dots, m_r$ with $N = \prod m_i$, the CRT combination of the residues of $x$ is congruent to $x$ modulo $N$ and is at most $(N-1)^2$, so if $N^2 \le p^k$ a remainder gadget over $\mathbb{Z}/p^{2k+1}$ recovers $x \bmod N$ without wrap-around; (iii) *exact constant division*: for a public integer $N \ge 1$, let $k_E = \lceil \log_p N \rceil$ and $c = \lceil p^{k + k_E}/N \rceil$; over $\mathbb{Z}/p^{2k+1}$, the gate $\mathrm{div}^*_N(x) = \lfloor (c x \bmod p^{2k+1})/p^{k + k_E} \rfloor$ (a multiplication by the public constant $c$ followed by dropping the $k + k_E$ low base-$p$ digits) equals $\lfloor x/N \rfloor$, and $\mathrm{mod}^*_N(x) = x - N\,\mathrm{div}^*_N(x)$ equals $x \bmod N$, for every input $x < p^k$.

## Proof sketch

Each part is an integer identity checked on canonical representatives; the no-wrap conditions ensure the products computed modulo the large prime power equal the integer products.

## Depends on

- [Affine wire labels for arithmetic garbling](affine-wire-labels.md)

## Sources

- Hanjun Li and Tianren Liu, "How to Garble Mixed Circuits that Combine Boolean and Arithmetic Computations", Advances in Cryptology – EUROCRYPT 2024, Part VI, 2024.
