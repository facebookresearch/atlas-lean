# Wiedemann towers of binary fields

Define $\mathcal{T}_0=\mathbb{F}_2$ and, for $\iota\ge 0$, $\mathcal{T}_{\iota+1}=\mathcal{T}_\iota[X_\iota]/(X_\iota^{2}+X_{\iota-1}X_\iota+1)$, with the convention $X_{-1}=1$. Then $\mathcal{T}_\iota$ is the field with $2^{2^{\iota}}$ elements, each $\mathcal{T}_\iota$ is a subfield of $\mathcal{T}_{\iota+1}$, and every element of $\mathcal{T}_\iota$ has a canonical representation as a $2^{\iota}$-bit string via the multilinear basis $\{\prod_{j\in S}X_j:S\subseteq\{0,\dots,\iota-1\}\}$ over $\mathbb{F}_2$.

## Sources

- Doug Wiedemann, "An Iterated Quadratic Extension of GF(2)", Fibonacci Quarterly (1988).
- Benjamin E. Diamond, Jim Posen, "Succinct Arguments over Towers of Binary Fields", EUROCRYPT (2025), IACR ePrint 2023/1784.
