# A-posteriori error bounds for approximate spectral exponentials of a reversible rate matrix

Let $Q$ be a rate matrix on a finite set $\{1,\ldots,n\}$ in [detailed balance](is-detailed-balance.md) with a probability vector $\pi$ with all $\pi_i>0$. Put $D=\operatorname{diag}(\pi)$ and $S=D^{1/2}QD^{-1/2}$. Then $S$ is symmetric with eigenvalues $\le0$, so $\lVert e^{sS}\rVert_2\le1$ for $s\ge0$, and $e^{tQ}=D^{-1/2}e^{tS}D^{1/2}$. Let $V$ be an invertible real $n\times n$ matrix and $\Lambda$ a real diagonal matrix (approximate eigenvectors and eigenvalues of $S$), and set

$$R=SV-V\Lambda,\qquad E=V^{\top}V-I,\qquad \kappa=\lVert V\rVert_2\lVert V^{-1}\rVert_2,\qquad \lambda_+=\max\bigl(0,\max_i\Lambda_{ii}\bigr),$$

with $\lVert\cdot\rVert_2$ the spectral norm. Two approximants must be distinguished, since $e^{tV\Lambda V^{\top}}\ne Ve^{t\Lambda}V^{\top}$ unless $V$ is orthogonal. For $t\ge0$:

- **(A)** $X_A(t)=Ve^{t\Lambda}V^{-1}=e^{tV\Lambda V^{-1}}$ satisfies $X_A(0)=I$ and

    $$\lVert e^{tS}-X_A(t)\rVert_2\le t\,\lVert R\rVert_2\,\lVert V^{-1}\rVert_2\,\kappa\,e^{t\lambda_+}.$$

- **(B)** $X_B(t)=Ve^{t\Lambda}V^{\top}$ satisfies $X_B(0)=VV^{\top}$, with $\lVert I-VV^{\top}\rVert_2=\lVert E\rVert_2$, and

    $$\lVert e^{tS}-X_B(t)\rVert_2\le\bigl(t\,\lVert R\rVert_2\,\lVert V^{-1}\rVert_2+\lVert E\rVert_2\bigr)\,\kappa\,e^{t\lambda_+}.$$

- **(C)** If $\lVert E\rVert_2<1$, then $\lVert V\rVert_2\le\sqrt{1+\lVert E\rVert_2}$, $\lVert V^{-1}\rVert_2\le(1-\lVert E\rVert_2)^{-1/2}$ and $\kappa\le\sqrt{(1+\lVert E\rVert_2)/(1-\lVert E\rVert_2)}$.
- **(D)** $\lambda_{\max}(V\Lambda V^{\top})\le\lambda_+\lVert V\rVert_2^2$, hence $\le\lambda_+(1+\lVert E\rVert_2)$ when $\lVert E\rVert_2<1$ (used only when comparing with $e^{tV\Lambda V^{\top}}$).
- **(E)** For $X\in\{X_A,X_B\}$ and all $i,j$,

    $$\bigl|(e^{tQ})_{ij}-(D^{-1/2}X(t)D^{1/2})_{ij}\bigr|\le\sqrt{\pi_j/\pi_i}\;\lVert e^{tS}-X(t)\rVert_2 .$$

Exact orthonormal eigenpairs give $R=0$ and $E=0$, and both bounds vanish.

## Depends on

- [Detailed balance](is-detailed-balance.md)

## Proof depends on

- [Spectral formula for a reversible rate matrix](symmetrized-spectral-formula-for-p-t-exp-tq-of-a.md)

## Expansion

A full proof page must establish:

- Symmetry and nonpositivity of the spectrum of $S$, and $e^{tQ}=D^{-1/2}e^{tS}D^{1/2}$.
- (A): with $B=V\Lambda V^{-1}$, $S-B=RV^{-1}$; the Duhamel formula $e^{tS}-e^{tB}=\int_0^1t\,e^{stS}(S-B)e^{(1-s)tB}\,ds$; and $\lVert e^{rB}\rVert_2\le\kappa e^{r\lambda_+}$ for $r\ge0$.
- (B): $V^{\top}=(I+E)V^{-1}$, so $X_B-X_A=Ve^{t\Lambda}EV^{-1}$; and $VV^{\top}$, $V^{\top}V$ have the same spectrum.
- (C) from the singular values of $V$; (D) from $x^{\top}V\Lambda V^{\top}x\le\lambda_+\lVert V^{\top}x\rVert^2$; (E) from $|M_{ij}|\le\lVert M\rVert_2$.
- The $1\times1$ probe $S=0$, $V=2$, $\Lambda=1$, $t=1$: $R=-2$, $E=3$, $\kappa=1$, $\lVert V^{-1}\rVert_2=\tfrac12$; (A) true error $e-1\approx1.718$ against the bound $e\approx2.718$; (B) true error $4e-1\approx9.873$ against $4e\approx10.873$; (B) at $t=0$ true error $3$ equals the bound $3$.
- A numerical check on a perturbed four-state Jukes–Cantor rate matrix, comparing both bounds with computed spectral-norm errors at several times.

## Sources

- C. Moler and C. Van Loan, *Nineteen dubious ways to compute the exponential of a matrix, twenty-five years later*, SIAM Review (2003) (eigenvector methods for the matrix exponential; background).
