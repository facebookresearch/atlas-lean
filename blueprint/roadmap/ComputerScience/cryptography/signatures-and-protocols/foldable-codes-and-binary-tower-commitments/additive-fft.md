# Additive FFT in the novel polynomial basis

Let $U\subseteq\mathbb{F}_{2^{k}}$ be an $\mathbb{F}_2$-linear subspace of dimension $\ell$ with basis $\beta_0,\dots,\beta_{\ell-1}$, let $W_i(X)=\prod_{u\in\mathrm{span}(\beta_0,\dots,\beta_{i-1})}(X-u)$ be the subspace vanishing polynomials (which are $\mathbb{F}_2$-linearized), and define the novel basis $X_j(X)=\prod_{i:\,j_i=1}W_i(X)/W_i(\beta_i)$ for $j<2^{\ell}$ with binary digits $j_i$. Then any polynomial $\sum_{j<2^{\ell}}a_jX_j(X)$ can be evaluated on all of $U$ (and on any affine shift of $U$) with $O(2^{\ell}\ell)$ field additions and multiplications.

## Proof sketch

The normalized $\widehat{W}_i=W_i/W_i(\beta_i)$ are linear maps, so the polynomial splits as $P_0(\widehat{W}_{\ell-1})+\widehat{W}_{\ell-1}P_1$-style recursions on a subspace of half dimension; the two cosets of the hyperplane are handled by one butterfly per point, giving $\ell$ layers of $2^{\ell}$ operations.

## Proof depends on

- [Wiedemann towers of binary fields](binary-tower.md)

## Sources

- Sian-Jheng Lin, Wei-Ho Chung, Yunghsiang S. Han, "Novel Polynomial Basis and Its Application to Reed-Solomon Erasure Codes", FOCS (2014).
- Benjamin E. Diamond, Jim Posen, "Succinct Arguments over Towers of Binary Fields", EUROCRYPT (2025), IACR ePrint 2023/1784.
