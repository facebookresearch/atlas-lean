# Packing small-field elements into tower-field elements

For $\iota\le\tau$, $\mathcal{T}_\tau$ is a $2^{\tau-\iota}$-dimensional vector space over $\mathcal{T}_\iota$ with basis the monomials in $X_\iota,\dots,X_{\tau-1}$, and the identification of $2^{\tau-\iota}$ consecutive $\mathcal{T}_\iota$-elements with one $\mathcal{T}_\tau$-element is $\mathcal{T}_\iota$-linear and agrees with the canonical bit representation. Consequently a multilinear polynomial with coefficients in $\mathcal{T}_\iota$ in $\ell$ variables is equivalently a multilinear polynomial over $\mathcal{T}_\tau$ in $\ell-(\tau-\iota)$ variables, and multiplication in $\mathcal{T}_{\iota+1}$ reduces to three multiplications in $\mathcal{T}_\iota$ by Karatsuba.

## Proof sketch

Each extension step is quadratic, so the dimension doubles per level. The defining polynomial $X_\iota^{2}+X_{\iota-1}X_\iota+1$ gives $(a+bX)(c+dX)=ac+bd+(ad+bc+bdX_{\iota-1})X$ using $X^{2}=X_{\iota-1}X+1$, computable from $ac$, $bd$ and $(a+b)(c+d)$.

## Depends on

- [Wiedemann towers of binary fields](binary-tower.md)

## Sources

- Doug Wiedemann, "An Iterated Quadratic Extension of GF(2)", Fibonacci Quarterly (1988).
- Benjamin E. Diamond, Jim Posen, "Succinct Arguments over Towers of Binary Fields", EUROCRYPT (2025), IACR ePrint 2023/1784.
