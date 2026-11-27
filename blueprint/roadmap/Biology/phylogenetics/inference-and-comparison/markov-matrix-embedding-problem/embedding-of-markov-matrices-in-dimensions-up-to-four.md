# Embedding of Markov matrices in dimensions up to four

**Setting.** A $d \times d$ *Markov matrix* $M$ has nonnegative entries and unit row sums; a *generator* (rate matrix) $Q$ has nonnegative off-diagonal entries and zero row sums. $M$ is *embeddable* if $M = e^{Q}$ for some generator $Q$, i.e. if $M$ is the transition matrix at time $1$ of a time-homogeneous continuous-time Markov chain. Write $A = M - \mathbb{1}$.

**Theorem.**
1. *(Kendall, $d = 2$.)* $M = \begin{pmatrix} 1-a & a \\ b & 1-b \end{pmatrix}$ with $a, b \in [0,1]$ is embeddable if and only if $\det M > 0$, equivalently $0 \le a + b < 1$. The generator is then unique:

$$Q = -\frac{\log(1 - a - b)}{a + b}\, (M - \mathbb{1}).$$

2. *($d = 3$, real cyclic case.)* If $M$ is cyclic with real spectrum, $M$ is embeddable if and only if all eigenvalues of $M$ are positive and the real matrix $Q = \log(\mathbb{1} + A) = \alpha A + \beta A^2$ (explicit $\alpha, \beta$ from the spectrum) is a generator; the embedding is then unique.
3. *($d = 3$, complex case.)* If $\sigma(M) = \{1, \lambda, \bar\lambda\}$ with $\lambda \notin \mathbb{R}$, put $\mu = \lambda - 1$ and $z_k = \log\lambda + 2\pi i k$ for $k \in \mathbb{Z}$. The real logarithms of $M$ are exactly $R_k = \alpha_k A + \beta_k A^2$ with

$$\begin{pmatrix} \alpha_k \\ \beta_k \end{pmatrix} = \frac{1}{|\mu|^2(\bar\mu - \mu)} \begin{pmatrix} \bar\mu^2 z_k - \mu^2 \bar z_k \\ -\bar\mu z_k + \mu \bar z_k \end{pmatrix}.$$

$M$ is embeddable if and only if $0 < |\lambda| < 1$ and some $R_k$ is a generator. Only finitely many $R_k$ are generators, at most $\big\lfloor 1 - \frac{\log\det M}{2\pi\sqrt3}\big\rfloor$ of them.
4. *(Equal-input model, $d = 4$.)* For $M_c = (1 - c)\mathbb{1} + C$, where $C$ has four equal rows $(c_1, \dots, c_4)$ with $c_i \ge 0$ and $c = \sum_i c_i$, $M_c$ is embeddable if and only if $0 \le c < 1$. Then $M_c = e^Q$ with the equal-input generator $Q = \frac{-\log(1 - c)}{c}\, A$ ($Q = 0$ for $c = 0$); for $c > 0$ there are at most finitely many other embeddings, none of equal-input type.

## Depends on

- [F81 rate matrix](../../time-reversible-nucleotide-substitution-models/f81-rate.md)

## Expansion

Embeddability asks whether a substitution matrix estimated over one branch is consistent with a constant-rate process. In $d = 2$ the only logarithm is the principal one, and it has the generator sign pattern exactly when $\det M > 0$. In $d = 3$ a cyclic matrix has all its logarithms in the algebra spanned by $\mathbb{1}, A, A^2$; real eigenvalues force the principal branch, while a complex pair allows the branches $z_k$, and the generator condition can only hold while $|\operatorname{Im} z_k|$ is controlled by $-\log\det M$, which bounds the number of embeddings. For equal-input matrices $A^2 = -cA$, so the principal logarithm is a scalar multiple of $A$ and is a generator exactly when $c < 1$; the same structure gives the Tamura–Nei and Kimura three-parameter cases.

## Sources

- Michael Baake and Jeremy Sumner, "Embedding of Markov matrices for $d \leqslant 4$", Journal of Mathematical Biology 89 (2024), 23, <https://doi.org/10.1007/s00285-024-02112-w>; numbering as in arXiv:2311.02596: Theorem 2.4, Propositions 3.10–3.11 (with the coefficient formula for $\alpha_k, \beta_k$), Corollary 5.1.
