# Positive semi-definiteness of the generic string kernel

**Definitions.** Let $\Sigma$ be the amino-acid alphabet and $\psi : \Sigma \to \mathbb R^d$ an encoding of residues by physico-chemical descriptors; for $y = (y_1,\dots,y_l) \in \Sigma^l$ let $\psi_l(y) \in \mathbb R^{ld}$ be the concatenation of $\psi(y_1),\dots,\psi(y_l)$. For strings $x, x'$, an integer $L \ge 1$ and $\sigma_p, \sigma_c > 0$, the generic string (GS) kernel is

$$\mathrm{GS}(x,x',L,\sigma_p,\sigma_c) = \sum_{l=1}^{L}\ \sum_{i=0}^{|x|-l}\ \sum_{j=0}^{|x'|-l} e^{-\frac{(i-j)^2}{2\sigma_p^2}}\, e^{-\frac{\|\psi_l(x_{i+1..i+l}) - \psi_l(x'_{j+1..j+l})\|^2}{2\sigma_c^2}}.$$

**Theorem.** For each $l \in \{1,\dots,L\}$ let $K_l : \Sigma^l \times \Sigma^l \to \mathbb R$ be a symmetric positive semi-definite kernel, and let $A : \mathbb R \to \mathbb R$ be a self-convolution, i.e. $A(z - z') = \int_{-\infty}^{\infty} B(z - t)\,B(z' - t)\,dt$ for some $B$ and all $z, z'$. Then

$$K(x,x') = \sum_{l=1}^{L}\ \sum_{i=0}^{|x|-l}\ \sum_{j=0}^{|x'|-l} A(i - j)\, K_l\big((x_{i+1},\dots,x_{i+l}),(x'_{j+1},\dots,x'_{j+l})\big)$$

is symmetric positive semi-definite on strings of length at least $L$.

**Corollary.** The GS kernel is symmetric positive semi-definite for all $(L,\sigma_p,\sigma_c)$, so there is a feature map $\phi$ with $\mathrm{GS}(x,x') = \phi(x)\cdot\phi(x')$; in particular the kernel ridge regression solution $\alpha = (K + I/C)^{-1} e$ exists and is unique for every $C > 0$.

**Computation.** With $E(a,a') = \|\psi(a) - \psi(a')\|^2$ precomputed for all residue pairs, $\|\psi_l(y) - \psi_l(y')\|^2 = \sum_{k=1}^l E(y_k,y'_k)$, and

$$\mathrm{GS}(x,x',L,\sigma_p,\sigma_c) = \sum_{i}\sum_{j} e^{-\frac{(i-j)^2}{2\sigma_p^2}}\, B_{i,j},\qquad B_{i,j} = \sum_{l=1}^{\min(L,|x|-i,|x'|-j)} e^{-\frac{1}{2\sigma_c^2}\sum_{k=1}^{l} E(x_{i+k},x'_{j+k})},$$

where the inner sums of $B_{i,j}$ share prefixes and are accumulated incrementally in $l$.

## Depends on

- [Positive-definite kernel](../../../../Analysis/hilbert-spaces/positive-definite-kernels/is-pos-def-kernel.md)

## Proof depends on

- [Inner products of features form a positive-definite kernel](../../../../Analysis/hilbert-spaces/positive-definite-kernels/is-pos-def-kernel-of-eq-inner.md)
- [Regularized kernel matrices are invertible](../../../../ComputerScience/machine-learning/supervised-learning/gaussian-process-regression/is-unit-det-kernel-matrix-add.md)

## Expansion

Write $A(i - j) = \langle B(i - \cdot), B(j - \cdot)\rangle_{L^2}$ and $K_l(u,v) = \langle \phi_l(u), \phi_l(v)\rangle$; then $K(x,x') = \sum_l \big\langle \sum_i B(i - \cdot)\otimes \phi_l(x_{i+1..i+l}),\ \sum_j B(j - \cdot)\otimes\phi_l(x'_{j+1..j+l})\big\rangle$, an inner product of explicit feature vectors, hence positive semi-definite. For the GS kernel, $K_l$ is a Gaussian RBF kernel on $\mathbb R^{ld}$, and the Gaussian shift penalty is a self-convolution because convolving two Gaussians gives a Gaussian:

$$e^{-\frac{(i-j)^2}{2\sigma_p^2}} = \frac{1}{\sigma_p}\sqrt{\frac{2}{\pi}} \int_{-\infty}^{\infty} e^{-\frac{(i-t)^2}{\sigma_p^2}}\, e^{-\frac{(j-t)^2}{\sigma_p^2}}\,dt.$$

Letting $\sigma_p \to 0$ forces aligned positions (weighted-degree type kernels), $\sigma_p \to \infty$ ignores positions (spectrum type kernels), and $\sigma_c \to 0$ turns residue similarity into exact matching.

## Sources

- S. Giguère, M. Marchand, F. Laviolette, A. Drouin, J. Corbeil, "Learning a peptide-protein binding affinity predictor with kernel ridge regression", BMC Bioinformatics 14:82 (2013), Eq (1), GS kernel definition, Theorem 1 and Eqs (5)–(9), <https://doi.org/10.1186/1471-2105-14-82>, PMCID PMC3651388.
