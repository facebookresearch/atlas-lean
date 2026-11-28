# Eigenvalue characterization of model embeddability for symmetric group-based models

**Setting.** Let $G$ be a finite additive abelian group (the states; e.g. $\mathbb Z_2 \times \mathbb Z_2$ for nucleotides with $A = (0,0)$, $T = (0,1)$, $C = (1,0)$, $G = (1,1)$), $\mathcal L$ a set of labels and $L : G \to \mathcal L$ a labeling function. A $(G, L)$-rate matrix has entries $Q_{g,h} = \psi(h - g)$ for a vector $\psi \in \mathbb R^G$ with $\sum_g \psi(g) = 0$, $\psi(g) \ge 0$ for $g \ne 0$, and $\psi(g) = \psi(h)$ whenever $L(g) = L(h)$; a $(G, L)$-Markov matrix has entries $P_{g,h} = f(h - g)$ for a probability vector $f$ with the same label symmetries. $L$ is *symmetric* if $L(g) = L(-g)$. Let $K$ be the discrete Fourier transform matrix, $K_{g,h} = \hat g(h)$ (characters of $G$). $L$ is **$G$-compatible** if $K$ and $K^{-1}$ preserve its symmetries: $K_{g,:}x_L = K_{h,:}x_L$ and $(K^{-1})_{g,:}x_L = (K^{-1})_{h,:}x_L$ whenever $L(g) = L(h)$, where $x_L = (x_{L(g)})_{g}$. The labelings of the Cavender–Farris–Neyman, Jukes–Cantor, Kimura 2- and 3-parameter models are $G$-compatible. $P$ is **$(G,L)$-embeddable** if $P = e^Q$ for some $(G,L)$-rate matrix $Q$.

**Theorem.** Let $L$ be symmetric and $G$-compatible and $P$ a $(G,L)$-Markov matrix with eigenvalue vector $\lambda = (\lambda_g)_{g \in G}$ (the Fourier transform of $f$). Then $P$ is $(G,L)$-embeddable if and only if

$$\lambda_0 = 1, \qquad \lambda_g > 0 \ \ \forall g, \qquad \lambda_g = \lambda_h \text{ whenever } L(g) = L(h), \qquad \prod_{h \in G}\lambda_h^{\operatorname{Re}(K_{g,h})} \ge 1 \ \ \forall g \ne 0.$$

Moreover, a $G$-compatible labeling never gives the identity element the label of another element. For example, the CFN matrix $\begin{pmatrix} a & b \\ b & a\end{pmatrix}$ is embeddable iff $0 < a - b \le 1$.

## Depends on

- [Entries of the K80 rate matrix](../../kimura-two-parameter-model/k80-rate-apply.md)

## Expansion

Every $(G,L)$-rate matrix and Markov matrix is a group convolution, hence diagonalized by $K$: $Q = K\operatorname{diag}(\check\psi)K^{-1}$ and $P = e^Q = K\operatorname{diag}(e^{\check\psi})K^{-1}$, where $\check\psi = K\psi$ is real for symmetric labelings. So $P$ is embeddable iff its eigenvalue vector is the coordinatewise exponential of the transform of an admissible $\psi$. The admissible transforms are $\{\check\psi : \check\psi(0) = 0,\ (K^{-1}\check\psi)(g) \ge 0 \ (g \ne 0),\ \check\psi \text{ constant on label classes}\}$, where $G$-compatibility guarantees that the label symmetries pass through the transform. Exponentiating, $\check\psi(0) = 0$ becomes $\lambda_0 = 1$, positivity of the exponential gives $\lambda_g > 0$, and each linear inequality $a^{\top}\check\psi \ge 0$ becomes $\prod_h \lambda_h^{a_h} \ge 1$; since $K^{-1} = \bar K/|G|$ and the relevant vectors are real and symmetric, the exponents may be taken as $\operatorname{Re}(K_{g,h})$. The logarithm is unique on the positive reals, so the characterization is exact with no branch ambiguity. Because the conditions are on eigenvalues only, the embeddable matrices form a semialgebraic set whose volume relative to all model Markov matrices can be computed; for cyclic groups the result coincides with the characterization of embeddable circulant matrices.

## Sources

- M. Ardiyansyah, D. Kosta, K. Kubjas, "The model-specific Markov embedding problem for symmetric group-based models", Journal of Mathematical Biology 83 (2021) 33, Definition 2, Example 3, Lemmas 4–5, Theorem 1 (Eqs. (4.1)–(4.2)) and the CFN example, <https://doi.org/10.1007/s00285-021-01656-5>, PMCID PMC8429190.
