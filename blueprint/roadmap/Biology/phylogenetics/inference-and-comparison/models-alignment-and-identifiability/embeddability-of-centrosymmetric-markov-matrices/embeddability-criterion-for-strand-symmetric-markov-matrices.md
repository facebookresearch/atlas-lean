# Embeddability criterion for strand-symmetric (4×4 centrosymmetric) Markov matrices

**Setting.** A *Markov matrix* is a nonnegative real square matrix with unit row sums; a *rate matrix* has zero row sums and nonnegative off-diagonal entries. A Markov matrix $M$ is *embeddable* if $M=\exp(Q)$ for some rate matrix $Q$ (a *Markov generator*), i.e. if it is consistent with a time-homogeneous continuous-time substitution process. A real $n\times n$ matrix $A=(a_{ij})$ is *centrosymmetric* (CS) if $a_{ij}=a_{n+1-i,\,n+1-j}$. For nucleotides ordered $A,C,G,T$, $4\times4$ CS Markov matrices are exactly the transition matrices of the **strand-symmetric model** (complementary substitutions on the two DNA strands occur with equal probability):

$$M=\begin{pmatrix}m_{11}&m_{12}&m_{13}&m_{14}\\ m_{21}&m_{22}&m_{23}&m_{24}\\ m_{24}&m_{23}&m_{22}&m_{21}\\ m_{14}&m_{13}&m_{12}&m_{11}\end{pmatrix};$$

they contain the Kimura 3-parameter, Kimura 2-parameter and Jukes–Cantor matrices. With

$$S=\begin{pmatrix}1&0&0&1\\0&1&1&0\\0&1&-1&0\\1&0&0&-1\end{pmatrix},\qquad S^{-1}MS=\mathrm{diag}\!\left(\begin{pmatrix}\lambda&1-\lambda\\1-\mu&\mu\end{pmatrix},\begin{pmatrix}\alpha&\alpha'\\ \beta'&\beta\end{pmatrix}\right),$$

where $\lambda=m_{11}+m_{14}$, $\mu=m_{22}+m_{23}$, $\alpha=m_{22}-m_{23}$, $\alpha'=m_{21}-m_{24}$, $\beta=m_{11}-m_{14}$, $\beta'=m_{12}-m_{13}$. Let $\Delta=(\alpha-\beta)^2+4\alpha'\beta'$; the eigenvalues of $M$ are $1$, $\lambda_1=\lambda+\mu-1$ and $\lambda_{2,3}=\tfrac12\bigl((\alpha+\beta)\pm\sqrt\Delta\bigr)$.

**Theorem.** Let $M$ be a diagonalizable $4\times4$ CS Markov matrix with distinct eigenvalues. Put $x=\log\lambda_1$, $y_k=\log\lambda_2+2k\pi i$, $z_k=\log\lambda_3-2k\pi i$, with $k=0$ if $\Delta>0$ and $k\in\mathbb{Z}$ if $\Delta<0$, and

$$\alpha_1=\tfrac{1-\lambda}{2-\lambda-\mu}x,\quad \beta_1=\tfrac{1-\mu}{2-\lambda-\mu}x,\quad \delta(k)=\tfrac12\Bigl((y_k+z_k)+(\alpha-\beta)\tfrac{y_k-z_k}{\sqrt\Delta}\Bigr),\quad \gamma(k)=\tfrac12\Bigl((y_k+z_k)-(\alpha-\beta)\tfrac{y_k-z_k}{\sqrt\Delta}\Bigr),$$

$$\varepsilon(k)=\alpha'\tfrac{y_k-z_k}{\sqrt\Delta},\qquad \phi(k)=\beta'\tfrac{y_k-z_k}{\sqrt\Delta}.$$

Every real logarithm of $M$ equals $S\,\mathrm{diag}\!\left(\begin{pmatrix}\alpha_1&-\alpha_1\\-\beta_1&\beta_1\end{pmatrix},\begin{pmatrix}\delta(k)&\varepsilon(k)\\ \phi(k)&\gamma(k)\end{pmatrix}\right)S^{-1}$ and is itself centrosymmetric. Consequently $M$ is embeddable if and only if, for $k=0$ when $\Delta>0$ or for some $k\in\mathbb{Z}$ when $\Delta<0$,

$$\lambda_1>0,\quad (\alpha+\beta)^2>\Delta,\quad |\phi(k)|\le-\alpha_1,\quad |\varepsilon(k)|\le-\beta_1,\quad \gamma(k)\le\alpha_1,\quad \delta(k)\le\beta_1 .$$

In particular such an $M$ is embeddable iff it has a strand-symmetric generator (model embeddability coincides with general embeddability). Moreover, there is a positive-measure set of embeddable $4\times4$ CS Markov matrices whose Markov generator is **not** unique (rates not identifiable), all of whose generators are CS.

## Depends on

- [Jukes–Cantor transition matrix as a stochastic matrix](../../../jukes-cantor-model/jc-stochastic-matrix.md)

## Expansion

Conjugation by $S$ splits $M$ into a $2\times2$ Markov block and a $2\times2$ block $M_2$ that need not be Markov. By the enumeration of real logarithms of a Markov matrix with distinct eigenvalues, a real logarithm must use the principal branch on the real eigenvalues, forcing $\lambda_1>0$ (equivalently $\lambda+\mu>1$) for the Markov block; for $M_2$, real distinct eigenvalues ($\Delta>0$) must be positive (giving $\lambda_2\lambda_3>0$, i.e. $(\alpha+\beta)^2>\Delta$), while a conjugate pair ($\Delta<0$) admits the branches $\log_k,\log_{-k}$. Transforming back gives the CS entries $q_{11}=\tfrac12(\alpha_1+\gamma)$, $q_{12}=\tfrac12(-\alpha_1+\phi)$, $q_{13}=\tfrac12(-\alpha_1-\phi)$, $q_{14}=\tfrac12(\alpha_1-\gamma)$ and analogously for row $2$; nonnegativity of the off-diagonal entries is the four displayed inequalities. Specialized to Kimura 3-parameter matrices with eigenvalues $p,q,r$ the criterion becomes $r>0$, $pq>0$, $|\log(q/p)|\le-\log r$, $\log(pq)\le\log r$. Non-identifiability comes from complex eigenvalue pairs, where two different branches $k$ can both give rate matrices on an open set.

## Sources

- Muhammad Ardiyansyah, Dimitra Kosta and Jordi Roca-Lacostena, "Embeddability of centrosymmetric matrices capturing the double-helix structure in natural and synthetic DNA", Journal of Mathematical Biology 86 (2023), 69, <https://doi.org/10.1007/s00285-023-01895-8>; numbering as in arXiv:2202.05889: Section 3: Theorem 3.6, Theorem 3.7, Proposition 3.9, and Proposition 2.6 (logarithm enumeration).
