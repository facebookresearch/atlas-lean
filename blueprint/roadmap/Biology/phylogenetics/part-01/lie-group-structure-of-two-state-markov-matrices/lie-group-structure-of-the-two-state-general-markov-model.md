# Lie group structure of the two-state general Markov model

The transition matrices of the two-state general Markov model of sequence evolution are the (column) Markov matrices

$$M = \begin{pmatrix} 1-a & b \\ a & 1-b \end{pmatrix}, \qquad \det M = 1 - a - b,$$

stochastic when $0 \le a, b \le 1$ (the binary-symmetric model is $a = b$). The invertible ones form the matrix Lie group $\mathcal G = \{M : a, b \in \mathbb R,\ a + b \neq 1\}$, with identity component $\mathcal G^0$.

**Results.**

(1) $\mathcal G^0 = \{M \in \mathcal G : \det M > 0\}$, and $\mathcal G$ is the disjoint union of $\mathcal G^0$ and one coset $P\mathcal G^0$ ($\mathcal G/\mathcal G^0 \cong \mathbb Z_2$), each diffeomorphic to the other; both are connected.

(2) Every element of $\mathcal G^0$ is an exponential of a rate matrix:

$$\mathcal G^0 = \Big\{ e^{Q} : Q = \begin{pmatrix} -\alpha & \beta \\ \alpha & -\beta \end{pmatrix},\ \alpha, \beta \in \mathbb R \Big\}.$$

(3) The Lie algebra $T_{\mathrm{id}}(\mathcal G^0)$, spanned by the elementary rate generators $L_1$ (state $1 \to 2$) and $L_2$ (state $2 \to 1$), has exactly one proper ideal, the line spanned by $L_1 - L_2$. It is the tangent space of the one-parameter normal subgroup

$$\mathcal H = \Big\{ h_s = \begin{pmatrix} 1-s & -s \\ s & 1+s \end{pmatrix} : s \in \mathbb R \Big\},$$

which is the kernel of $\det : \mathcal G^0 \to \mathbb R_{>0}$, so $\mathcal G^0/\mathcal H \cong \mathbb R_{>0}$.

(4) Every $M \in \mathcal G^0$ factors uniquely as a binary-symmetric evolution followed by an $\mathcal H$-perturbation:

$$M = e^{Qt}h_s = \frac12\begin{pmatrix} 1+\lambda & 1-\lambda \\ 1-\lambda & 1+\lambda \end{pmatrix}\begin{pmatrix} 1-s & -s \\ s & 1+s \end{pmatrix}, \qquad \lambda = e^{-t} = \det M, \quad s = \frac{a-b}{2\det M}.$$

$M$ is stochastic exactly when $|s| \le \tfrac12(e^t - 1)$.

So, in the two-state case, a Markov matrix with positive determinant is embeddable in a (possibly non-stochastic) continuous-time chain, the determinant measures elapsed time, and the single parameter $s$ measures departure from the binary-symmetric model; the leaves $e^{Qt}\mathcal H$ stratify the model by $\det M$.

## Expansion

$\det$ is a homomorphism $\mathcal G \to \mathbb R^\times$ whose sign separates the two components; the matrices with negative determinant form the coset of any reflection-like element. A $2\times2$ Markov generator $Q$ has eigenvalues $0$ and $-(\alpha + \beta)$, so $\det e^Q = e^{-(\alpha+\beta)} > 0$, and conversely solving $e^Q = M$ by diagonalization works whenever $\det M > 0$. For a path-connected matrix group with discrete centre, non-discrete normal subgroups correspond to nonzero ideals of the Lie algebra; computing the bracket $[L_1, L_2]$ in the two-dimensional algebra shows that $\langle L_1 - L_2 \rangle$ is the only proper ideal, and exponentiating it gives $\mathcal H$. The factorization picks, in each coset of $\mathcal H$, the unique symmetric representative with the same determinant.

## Sources

- Jeremy G. Sumner, "Lie geometry of 2x2 Markov matrices", arXiv (2012). Section 1 (definitions of $\mathcal G$, Results 1–6, Corollary 1, Theorem 1.1 on normal subgroups and ideals). <https://doi.org/10.48550/arXiv.1212.5311>. Published version: Journal of Theoretical Biology 327 (2013), 88–90, <https://doi.org/10.1016/j.jtbi.2013.01.026>; locators above refer to the arXiv version.
