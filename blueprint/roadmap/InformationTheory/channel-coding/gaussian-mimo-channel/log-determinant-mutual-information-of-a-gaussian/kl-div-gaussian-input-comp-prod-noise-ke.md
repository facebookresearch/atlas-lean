# Kl Div gaussian Input comp Prod noise Kernel output Law

Let $\iota$ and $\kappa$ be finite index sets with $\iota$ nonempty, let $H \in \mathbb{R}^{\iota \times \kappa}$, let $K \in \mathbb{R}^{\kappa \times \kappa}$ be positive semidefinite (possibly singular) and let $R \in \mathbb{R}^{\iota \times \iota}$ be positive definite. Let $P$ be the joint law on $\mathbb{R}^\kappa \times \mathbb{R}^\iota$ of $(X, HX + Z)$ with $X \sim \mathcal{N}(0, K)$ and $Z \sim \mathcal{N}(0, R)$ independent; that is, $P = \mathcal{N}(0, K) \otimes \kappa_R$ where the kernel $\kappa_R$ sends $x$ to the law of $Hx + Z$. Then, in nats,

$$D_{\mathrm{KL}}\left(P \,\middle\|\, \mathcal{N}(0, K) \otimes \mathcal{N}\left(0, H K H^{\mathsf{T}} + R\right)\right) = \frac{1}{2} \ln \frac{\det\left(R + H K H^{\mathsf{T}}\right)}{\det R},$$

a nonnegative number.
