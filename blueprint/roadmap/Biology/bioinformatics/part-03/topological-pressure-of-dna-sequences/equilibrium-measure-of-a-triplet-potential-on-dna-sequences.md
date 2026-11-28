# Equilibrium measure and Perron–Frobenius formula for the pressure of a triplet potential

**Setting.** Let $\mathcal A=\{A,C,G,T\}$, let $\psi:\mathcal A^3\to\mathbb R$ assign a weight to each of the $64$ nucleotide triplets, and let $\sigma$ be the left shift on $\Sigma=\mathcal A^{\mathbb N}$. For a finite word $w$ of length $4^n+n-1$ with set $SW_n(w)$ of distinct length-$n$ subwords, the **topological pressure** of $w$ is

$$
P(w,\psi)=\frac1n\log_4\Bigl(\sum_{u\in SW_n(w)}\exp\Bigl\{\sum_{i=1}^{n-2}\psi(u_iu_{i+1}u_{i+2})\Bigr\}\Bigr),
$$

which measures the weighted information content of $w$ (with $\psi\equiv0$ it is the normalized log-count of distinct $n$-subwords). Index the $16$ dinucleotides $w_1,\dots,w_{16}$ and define the $16\times16$ matrix $M_{ij}=e^{\psi(abc)}$ if $w_i=ab$ and $w_j=bc$, and $M_{ij}=0$ otherwise. By Perron–Frobenius, $M$ has a simple maximal eigenvalue $\lambda>0$ with positive right and left eigenvectors $r,l$. Set $P_{ij}=M_{ij}r_j/(\lambda r_i)$ (a stochastic matrix) and $p_i\propto l_ir_i$ (its stationary vector), and define the **equilibrium measure** $\mu_\psi$ on cylinders by

$$
\mu_\psi([x_1\cdots x_n])=p(x_1x_2)\,P(x_1x_2,x_2x_3)\cdots P(x_{n-2}x_{n-1},x_{n-1}x_n).
$$

**Theorem (Theorem 5.2).** $\mu_\psi$ is the unique equilibrium measure for $\psi$ on the full shift: it attains the supremum in the variational principle $P(\Sigma,\psi)=\sup_m\{h_m+\int\psi\,dm\}$ over shift-invariant probability measures, and

$$
P(\Sigma,\psi)=h_{\mu_\psi}+\int\psi\,d\mu_\psi=\log\lambda .
$$

**Theorem (Gibbs property, Theorem 5.3).** There is $C>1$ such that for every $n$ and every $w\in\mathcal A^n$,

$$
C^{-1}\le\frac{\mu_\psi([w])}{\exp\bigl\{-nP(\Sigma,\psi)+\sum_{i=1}^{n-2}\psi(w_iw_{i+1}w_{i+2})\bigr\}}\le C .
$$

**Theorem (maximal pressure, Theorem 5.4).** The largest possible pressure at length $n$, attained by a de Bruijn-type word containing every length-$n$ word, is $P_{\max}(\psi,n)=\frac1n\log_4\sum_{u\in\mathcal A^n}\exp\{\sum_{i=1}^{n-2}\psi(u_iu_{i+1}u_{i+2})\}=\log_4\|M^{n-2}\|^{1/n}$, and $\|M^{n-2}\|^{1/n}\to\lambda$ exponentially fast.

## Expansion

The sum over all length-$n$ words of $\exp\sum\psi$ is a sum of entries of $M^{n-2}$, since a word corresponds to a path of $n-2$ steps in the de Bruijn graph on dinucleotides; its growth rate is the spectral radius $\lambda$. The conjugated matrix $P$ is stochastic because $Mr=\lambda r$, and the telescoping product $\prod M_{i_ti_{t+1}}r_{i_{t+1}}/(\lambda r_{i_t})$ gives $\mu_\psi([w])=p_{i_1}r_{i_1}^{-1}r_{i_{n-1}}\lambda^{-(n-2)}e^{\sum\psi}$, which is the Gibbs bound with $C$ controlled by the ratios of the entries of $r$ and $p$. Gibbs measures for locally constant potentials on a mixing shift are unique equilibrium states. In the application, $\psi=\log$ of $64$ trained triplet weights is fitted so that the pressure of windows of about $66{,}000$ bp correlates with RefSeq coding sequence density on human chromosomes, and $\mu_\psi$ then scores introns versus exons.

## Proof depends on

- [Perron–Frobenius theorem for primitive nonnegative matrices](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius-for-primitive-nonnegative-matri.md)

## Sources

- D. Koslicki and D. J. Thompson, "Coding sequence density estimation via topological pressure", arXiv:1109.5999 (2011), Sections 2 (definition of topological pressure), 4 and 5 (equilibrium measure; Theorems 5.1–5.4), <https://doi.org/10.48550/arXiv.1109.5999>.
