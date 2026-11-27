# Uniformization stability is equivalent to a Jordan algebra

**Setting.** Let $\mathcal L_n=\{Q\in\mathrm{Mat}_n(\mathbb R):Q\mathbf 1=0\}$ be the zero row sum matrices and $\mathcal L_n^+\subset\mathcal L_n$ the rate matrices (non-negative off-diagonal entries) of continuous-time Markov chains on $n$ states, e.g. nucleotides. A *Markov model* is a subset $\mathcal L^+\subseteq\mathcal L_n^+$; it is *linear* if $\mathcal L^+=\mathcal L\cap\mathcal L_n^+$ for a linear subspace $\mathcal L\subseteq\mathcal L_n$, and then $\mathcal L^+=\mathrm{span}_{\mathbb R}(\mathcal L^+)\cap\mathcal L_n^+$. A subspace $\mathcal J$ of matrices is a *Jordan algebra* if it is closed under $A\odot B=AB+BA$; equivalently, it is closed under positive integer powers $C^k$.

**Definition.** $\mathcal L^+$ is *uniformization stable* if for all $t\ge 0$ and $Q\in\mathcal L^+$ there is $\hat Q\in\mathcal L^+$ with

$$e^{Qt}-I_n=\hat Q .$$

Equivalently, with the uniformization $e^{Qt}=\sum_{k\ge0}e^{-\lambda t}\frac{(\lambda t)^k}{k!}R^k$, $R=I_n+\lambda^{-1}Q$, both $e^{Qt}$ and the discrete-time matrix $R$ are of the form $I_n+(\text{rate matrix in the model})$.

**Theorem.** Let $\mathcal L^+$ be a linear Markov model. Then $\mathcal L^+$ is uniformization stable if and only if $\mathrm{span}_{\mathbb R}(\mathcal L^+)$ is a Jordan algebra.

**Examples.** Matrix algebras are both Jordan and Lie algebras, so equal-input models (e.g. the Felsenstein 1981 model), equivariant models such as Kimura 3ST, and group-based models are uniformization stable. For the 4-state equal-input model, $Q^2=-\lambda Q$ with $\lambda$ the sum of the four input rates, so $e^{Qt}-I=\frac{1-e^{-\lambda t}}{\lambda}Q$.

## Expansion

If the model is uniformization stable, then $\hat Q(t)=e^{Qt}-I_n$ lies in the closed subspace $\mathrm{span}(\mathcal L^+)$ for all $t\ge0$, so all derivatives at $t=0$, namely $Q^k$, lie there too. Since a linear model is a convex cone, $Q_1+Q_2\in\mathcal L^+$, and $Q_1Q_2+Q_2Q_1=(Q_1+Q_2)^2-Q_1^2-Q_2^2$ is in the span; bilinearity extends closure to the whole span. Conversely, closure under powers puts every partial sum of $e^{Qt}-I_n=\sum_{k\ge1}(Qt)^k/k!$ in the span, hence the limit, and $e^{Qt}$ is a Markov matrix so the limit is a rate matrix in $\mathcal L^+$.

## Sources

- L. Cooper, J. Sumner, "Uniformization stable Markov models and their Jordan algebraic structure", arXiv:2105.03558 (2021), <https://doi.org/10.48550/arXiv.2105.03558>. Section 2 (Definitions 2.13, 2.15, 2.28; Lemmas 2.16, 2.17, 2.22; Theorem 2.29; Example 2.30).
