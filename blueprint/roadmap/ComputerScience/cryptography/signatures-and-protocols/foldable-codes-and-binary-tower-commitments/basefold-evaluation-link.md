# Folding a foldable encoding computes a multilinear evaluation

Let $f=\mathrm{Enc}_d(\mathbf{m})$ be the foldable encoding of $\mathbf{m}\in\mathbb{F}^{2^{d}k_0}$, viewed (for $k_0=1$) as the coefficient vector of a multilinear polynomial $\bar{m}$ in $d$ variables in the ordering compatible with the recursive split $(m_0,m_1)$. For a challenge $r\in\mathbb{F}$ define the folded word $f'$ coordinatewise from $f_j,f_{j+n}$ as the encoding of $m_0+r\,m_1$; it is computable from two coordinates by inverting the $2\times 2$ system with matrix $\begin{pmatrix}1&t_j\\1&t'_j\end{pmatrix}$. After folding with $r_1,\dots,r_d$, the final encoded message is the scalar $\bar{m}(r_d,\dots,r_1)$ (in the variable order matching the split). Therefore running the folding IOPP in lockstep with a sum-check on $\bar{m}$ proves evaluation claims about $\bar{m}$.

## Proof sketch

Each fold replaces the message $(m_0,m_1)$ by $m_0+rm_1$, which is substituting the most significant variable of $\bar{m}$ by $r$. Linearity of encoding and the block structure of $G_{i+1}$ give the coordinatewise formula; invertibility of $T_i-T'_i$ makes the $2\times 2$ system solvable.

## Depends on

- [Foldable linear codes](foldable-linear-code.md)
- [Multilinear extension of a Boolean function](../../../../TheoryOfComputation/hierarchy-theorems-and-barriers/algebrization-barrier/multilinear-ext.md)

## Sources

- Hadas Zeilberger, Binyi Chen, Ben Fisch, "BaseFold: Efficient Field-Agnostic Polynomial Commitment Schemes from Foldable Codes", CRYPTO (2024), IACR ePrint 2023/1705.
