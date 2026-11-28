# Equivariant and group-based models are Lie Markov models

**Setting.** Work with $n\times n$ rate matrices with zero column sums, $\mathfrak L_{GM}=\{Q:\boldsymbol\theta^TQ=\mathbf 0^T\}$ with $\boldsymbol\theta=(1,\dots,1)^T$, spanned by the elementary rate matrices $L_{ij}$ ($i\ne j$, rate from state $j$ to state $i$). A rate-matrix model $\mathfrak L\subseteq\mathfrak L_{GM}$ is a **Lie Markov model** if it is a Lie algebra, i.e. closed under linear combinations and the commutator $[X,Y]=XY-YX$, that has a **stochastic basis**: a basis each of whose elements is a non-negative combination $\sum_{i\ne j}\alpha_{ij}L_{ij}$, $\alpha_{ij}\ge0$ (Definition 2.7). A Lie Markov model has the **symmetry of** a group $G\le\mathfrak S_n$ if it has a basis that conjugation by $K_\sigma$ permutes for every $\sigma\in G$, and $G$ is the largest subgroup of $\mathfrak S_n$ with this property (Definition 4.5). By the Baker–Campbell–Hausdorff formula, any product $e^{Q_1\tau_1}\cdots e^{Q_m\tau_m}$ with $Q_i\in\mathfrak L$ then equals $e^{\widehat Q t}$ for some $\widehat Q\in\mathfrak L$ (near the identity), so an inhomogeneous process has a homogeneous average within the model, and the transition-matrix model is multiplicatively closed.

**Result 1 and Result 2.** The rate matrices of the general time-reversible model do not form a Lie algebra, and the GTR transition-matrix model is not multiplicatively closed.

**Proposition 4.1 (equivariant models).** For a permutation group $G\le\mathfrak S_n$ with permutation matrices $K_\sigma$, the $G$-equivariant rate matrices

$$\mathfrak L^G=\{Q\in\mathfrak L_{GM}: K_\sigma QK_\sigma^{-1}=Q\ \text{for all}\ \sigma\in G\}$$

form a Lie Markov model, and $\mathfrak L^G$ is the tangent space at the identity of the $G$-equivariant Markov matrices (Lemma 4.3). Equivariance is equivalent to invariance under $G$ of the labelled rate graph of the model (Result 6).

**Proposition 4.3 (group-based models).** For a finite group $G$ (abelian or not) acting on itself by its regular representation, let $L_\sigma=K_\sigma-I$. The group-based model $\mathfrak L_G=\langle L_\sigma:\sigma\in G\rangle$ is a Lie Markov model, because

$$[L_\sigma,L_{\sigma'}]=K_{\sigma\sigma'}-K_{\sigma'\sigma}=L_{\sigma\sigma'}-L_{\sigma'\sigma}.$$

For abelian $G$ these are the usual group-based models, with off-diagonal rates depending only on $b-a$; $G=\mathbb Z_2\times\mathbb Z_2$ gives the Kimura three-parameter model.

**Result 5 (two states).** On two states there are exactly two Lie Markov models with the symmetry of $\mathfrak S_2$: the binary-symmetric model $\langle L_{12}+L_{21}\rangle$ of dimension $1$ and the general model $\langle L_{12},L_{21}\rangle$ of dimension $2$. (The span $\langle L_{12}-L_{21}\rangle$ is also invariant under $\mathfrak S_2$ but has no stochastic basis, so it is not a Lie Markov model.)

## Depends on

- [Stochastic cone of a Lie Markov model](stochastic-cone-of-a-lie-markov-model.md)

## Expansion

Conjugation by $K_\sigma$ is an algebra automorphism, so it commutes with brackets: if $X$ and $Y$ are fixed by every $K_\sigma$, so is $[X,Y]$. For group-based models, Lemma 4.8 identifies the tangent vectors as $K_\sigma-I$; the identity drops out of commutators, and the product of permutation matrices in the regular representation is again one, so brackets stay in the span. For GTR, two symmetric (uniform-$\boldsymbol\pi$) rate matrices have an antisymmetric commutator $X$, and $XD(\widehat{\boldsymbol\pi})=-D(\widehat{\boldsymbol\pi})X$ with positive $\widehat{\boldsymbol\pi}$ forces $X=0$ (Lemma 2.2), which fails for explicit non-commuting examples.

## Sources

- Jeremy G. Sumner, Jesús Fernández-Sánchez and Peter D. Jarvis, "Lie Markov models", arXiv:1105.4680 (2011), Section 2 (definitions, Lemma 2.2, Results 1–2), Section 2 (Definition 2.7), Section 3 (Result 5), Section 4 (Definitions 4.1–4.2 and 4.5, Lemma 4.3, Propositions 4.1–4.3, Lemma 4.8, Result 6; result numbers as in arXiv version 2), <https://doi.org/10.48550/arXiv.1105.4680>. Published version: Journal of Theoretical Biology 298 (2012), 16–31, <https://doi.org/10.1016/j.jtbi.2011.12.017>; locators above refer to the arXiv version.
