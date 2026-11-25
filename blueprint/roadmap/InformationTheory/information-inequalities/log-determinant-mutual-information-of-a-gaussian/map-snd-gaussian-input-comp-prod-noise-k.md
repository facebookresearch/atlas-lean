# Map snd gaussian Input comp Prod noise Kernel

Let $\iota$ and $\kappa$ be finite index sets, $H \in \mathbb{R}^{\iota \times \kappa}$, and let $K \in \mathbb{R}^{\kappa \times \kappa}$ and $R \in \mathbb{R}^{\iota \times \iota}$ be positive semidefinite (both possibly singular). Let $X \sim \mathcal{N}(0, K)$ and let the output given $X = x$ have the law of $Hx + Z$ with $Z \sim \mathcal{N}(0, R)$. Then the output $Y = HX + Z$ has law

$$Y \sim \mathcal{N}\left(0,\ H K H^{\mathsf{T}} + R\right);$$

that is, the second marginal of $\mathcal{N}(0, K) \otimes \kappa_R$ is $\mathcal{N}(0, H K H^{\mathsf{T}} + R)$, where $\kappa_R(x)$ is the law of $Hx + Z$.
