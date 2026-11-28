# Maximum likelihood estimation of log-affine models by detailed-balanced reaction networks

Let $A \in \mathbb{Z}^{d \times m}$ be a design matrix with $\mathbb{1} = (1,\dots,1)$ in its row span and $c \in \mathbb{R}^m_{>0}$. The *log-affine model* is

$$\mathcal{M}_{A,c} = \{p \in \operatorname{int} \Delta_{m-1} : \log p \in \log c + \operatorname{row}(A)\},$$

the probability vectors in the scaled positive toric variety $\mathcal{X}_{A,c} = \{(c_1 t^{a_1}, \dots, c_m t^{a_m}) : t \in \mathbb{R}^d_{>0}\}$ (log-linear when $c = \mathbb{1}$; the Hardy-Weinberg model is $A = \begin{pmatrix} 0 & 1 & 2 \\ 2 & 1 & 0 \end{pmatrix}$, $c = (1,2,1)$). For counts $u \in \mathbb{R}^m_{\ge 0} \setminus \{0\}$ with $\bar u = u / u_+$, Birch's theorem says that if $(\bar u + \ker A)_{>0} \ne \emptyset$ there is a unique $\hat p$ in the closure of $\mathcal{X}_{A,c}$ with $A \hat p = A \bar u$; it is positive and is the maximum likelihood estimate (MLE) of $u$ in $\mathcal{M}_{A,c}$.

**Construction.** For a finite set $\Lambda \subseteq \ker_{\mathbb{Z}}(A)$ spanning $\ker(A)$, write $\gamma = \gamma^+ - \gamma^-$ with $\gamma^\pm \ge 0$ of disjoint support and let $G_{\Lambda,c}$ be the mass-action system on species $X_1,\dots,X_m$ with the reversible reactions

$$\gamma^-_1 X_1 + \dots + \gamma^-_m X_m \;\underset{c^{\gamma^-}}{\overset{c^{\gamma^+}}{\rightleftharpoons}}\; \gamma^+_1 X_1 + \dots + \gamma^+_m X_m, \qquad \gamma \in \Lambda,$$

so that $\dot x = \sum_{\gamma \in \Lambda} \big(c^{\gamma^+} x^{\gamma^-} - c^{\gamma^-} x^{\gamma^+}\big)\, \gamma$.

**Theorem.** $G_{\Lambda,c}$ is detailed-balanced and its set of positive steady states is exactly $\mathcal{X}_{A,c}$. Its stoichiometric subspace is $\ker(A)$, so the rows of $A$ are conservation laws (the sufficient statistics). Consequently, if $(\bar u + \ker A)_{>0} \ne \emptyset$, the MLE $\hat p$ of $u$ is the unique steady state of $G_{\Lambda,c}$ in the positive compatibility class $(\bar u + \ker A)_{>0}$, and it is asymptotically stable. The deficiency of $G_\Lambda$ is $|\Lambda| - r - \dim \ker(A)$ with $r$ the cycle rank of its undirected graph; it is zero when $\Lambda$ is a vector-space basis of $\ker(A)$.

## Depends on

- [Birch's theorem, existence](../../complex-balancing-and-the-deficiency-zero-theore/exists-pos-sub-mem-log-orthogonal.md)
- [Birch's theorem, uniqueness](../../complex-balancing-and-the-deficiency-zero-theore/eq-of-sub-mem-log-orthogonal.md)
- [Horn-Jackson: the positive equilibria](../../complex-balancing-and-the-deficiency-zero-theore/positive-equilibria-eq.md)

## Expansion

The detailed-balance condition for the reaction pair of $\gamma$ is $c^{\gamma^+} x^{\gamma^-} = c^{\gamma^-} x^{\gamma^+}$, i.e. $(x/c)^{\gamma} = 1$; since $\Lambda$ spans $\ker A$, this holds for all $\gamma \in \Lambda$ exactly when $\log x - \log c \in (\ker A)^\perp = \operatorname{row}(A)$, i.e. $x \in \mathcal{X}_{A,c}$. Detailed-balanced systems have all positive steady states detailed balanced, one per compatibility class, each locally asymptotically stable, with the free energy as Lyapunov function. Starting the network at the normalized data $\bar u$, conservation of $A x$ keeps the trajectory in the class whose unique steady state satisfies Birch's conditions, so the network "computes" the MLE as its equilibrium.

## Sources

- Oskar Henriksson, Carlos Améndola, Jose Israel Rodriguez, Polly Y. Yu, "Maximum likelihood estimation of log-affine models using detailed-balanced reaction networks", *Journal of Mathematical Biology* 91(4) (2025), 34, Definition 2.1, Theorem 2.5 (Birch's theorem), Construction 4.1, Theorem 4.2, Remark 4.3, Theorem 4.6 and Theorem 5.5, <https://doi.org/10.1007/s00285-025-02262-5> (preprint arXiv:2411.07986).
