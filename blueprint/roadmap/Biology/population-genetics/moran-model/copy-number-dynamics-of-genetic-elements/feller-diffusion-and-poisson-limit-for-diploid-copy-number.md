# Feller diffusion and Poisson limit for diploid copy numbers of genetic elements

**Model.** A population of $N$ diploid individuals is tracked by the type of each individual, $k\in\mathbb N_0$, the number of copies of a genetic element (for example a transposable element) in its genome. At rate $N^2/2$ per reproduction event, a uniformly chosen individual dies and a uniformly chosen pair of parents with types $k,l$ produces one offspring of type $\mathrm{Bin}(k+l,\tfrac12)$, since each parental copy is inherited independently with probability $\tfrac12$. If $x=(x_k)$ is the type-frequency vector, the process jumps from $x$ to $x+(e_m-e_n)/N$ at rate

$$\frac{N^2}{2}\,x_n\sum_{k,l}x_kx_l\binom{k+l}{m}2^{-(k+l)} .$$

Let $X^N_t\in\mathcal P(\mathbb N_0)$ be the type distribution and $Z^N_t=\sum_k kX^N_t(k)$ the mean copy number.

**Theorem.** Suppose $Z^N_0\to z>0$ in probability and $\sup_N\mathbb E\big[\sum_k k^3X^N_0(k)\big]<\infty$. Then $(Z^N,X^N)\Rightarrow(Z,X)$, where $Z$ is the standard Feller branching diffusion

$$dZ_t=\sqrt{Z_t}\,dW_t,\qquad Z_0=z,$$

and $X_t=\mathrm{Poi}(Z_t)$ for every $t>0$. The convergence of $Z^N$ is in the Skorokhod topology. The convergence of $X^N$ is in the sense of weighted occupation measures $\int_0^\infty e^{-s}\delta_{X^N_s}\,ds$, since the Poisson shape is reached instantaneously and $X^N$ itself does not converge at $t=0$.

## Depends on

- [Feller's branching diffusion as the scaling limit of critical binary branching](../../../../Probability/branching-processes/linear-birth-death-process/feller-branching-diffusion-as-the-scaling-limit.md)

## Expansion

$Z^N$ is a martingale: binomial inheritance preserves the mean, and death removes a uniformly chosen type. Write $\rho_j(x) = \sum_{k \ge j} k(k-1)\cdots(k-j+1)\,x_k$ for the $j$-th **factorial** moment, so $\rho_1$ is the mean. The generator acting on functions $g \circ \rho_1$ of the first moment is $\tfrac12\big(\rho_1+\tfrac34(\rho_2-\rho_1^2)\big)g''(\rho_1)+o(1)$. Random mating with binomial thinning is a fast mixing step, of order $N^2$, that drives the type distribution to a Poisson law, for which the second factorial moment is $\rho_2=\rho_1^2$, that is $\rho_2-\rho_1^2=0$ (equivalently, variance equals mean). This collapses the generator to $\tfrac12\rho_1 g''$, which is Feller's diffusion. The Poisson limit is identified through the generating functions $\psi_s(x)=\sum_k x_k (1-s)^k$, $s\in[0,1]$, for which $\psi_s(\mathrm{Poi}(z)) = e^{-sz}$: a random law $Y$ with $\rho_1(Y)<\infty$ almost surely is $\mathrm{Poi}(\rho_1(Y))$ exactly when $\mathbb E[e^{-\lambda\psi_s(Y)}\mid\rho_1(Y)]=\exp(-\lambda e^{-s\rho_1(Y)})$ almost surely for all $\lambda\ge0$ and $s\in[0,1]$. A consequence is that, without transposition or selection, the total copy number behaves like a critical branching process and eventually dies out.

## Sources

- Peter Pfaffelhuber and Anton Wakolbinger, "A diploid population model for copy number variation of genetic elements", *Electronic Journal of Probability* 28 (2023), 1–15, <https://doi.org/10.1214/23-ejp934>. Numbering as in the preprint arXiv:2204.11140v3, <https://arxiv.org/abs/2204.11140v3>: Section 1 (model, jump rates (1.1) and convergence in measure (1.4)), Theorem 1.1 (joint convergence to Feller diffusion and Poisson profile), Definition 3.1 (factorial moments and generating functions) and Remark 3.2, Lemma 3.3 (generator on first moments), Corollary 3.6 (martingale property and moment bounds), Lemma 3.8 (characterization of random Poisson laws).
