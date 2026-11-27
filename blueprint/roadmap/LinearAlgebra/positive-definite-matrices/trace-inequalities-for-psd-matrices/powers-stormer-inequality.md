# The Powers–Størmer inequality for matrices

For positive semidefinite complex matrices $P$ and $Q$ of the same size,

$$
\operatorname{tr}\bigl((P-Q)^2\bigr)\le\bigl\|P^2-Q^2\bigr\|_1 ,
$$

where $\|\cdot\|_1$ is the trace norm (sum of singular values). Equivalently, $\|\sqrt A-\sqrt B\|_2^2\le\|A-B\|_1$ for positive semidefinite $A,B$. No trace normalization or invertibility is needed.

## Proof sketch

Let $X=P-Q=X_+-X_-$ with spectral projections $E,F$ onto the nonnegative and negative parts. Since $E$ commutes with $X$, $\operatorname{tr}(E(P^2-Q^2))=\operatorname{tr}(EPX)+\operatorname{tr}(EXQ)=\operatorname{tr}(X_+(P+Q))\ge\operatorname{tr}(X_+X)=\operatorname{tr}X_+^2$, because $\operatorname{tr}(X_+\cdot2Q)\ge0$. Symmetrically $\operatorname{tr}(F(Q^2-P^2))\ge\operatorname{tr}X_-^2$. Adding gives $\operatorname{tr}X^2\le\operatorname{tr}((E-F)(P^2-Q^2))\le\|P^2-Q^2\|_1$, as $E-F$ is a contraction.

## Sources

- Robert T. Powers, Erling Størmer, "Free states of the canonical anticommutation relations", Communications in Mathematical Physics, 1970.
- Gábor Szabó, Lise Wouters, "Equivariant property Gamma and the tracial local-to-global principle for C*-dynamics", Analysis & PDE, 2025.
