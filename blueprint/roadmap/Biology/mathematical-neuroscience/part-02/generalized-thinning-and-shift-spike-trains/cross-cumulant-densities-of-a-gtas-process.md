# Cross-cumulant densities of a GTaS process

**Setting.** Let $X$ be a GTaS counting process on $\mathbb{D}=\{1,\dots,N\}$ with mother rate $\lambda$, marking distribution $(p_D)_{D\subseteq\mathbb{D}}$ and shift distributions $(Q_D)_{D\subseteq\mathbb{D}}$. For a set $\bar D = \{i_1,\dots,i_k\} \subseteq \mathbb{D}$ of $k$ distinct indices and Borel sets $A_1,\dots,A_k \subseteq \mathbb{R}$, write $\kappa(\cdot,\dots,\cdot)$ for the joint cumulant and $Y_{\bar D}$ for the projection of $Y$ onto the coordinates in $\bar D$.

**Theorem.**

$$\kappa\bigl(X_{i_1}(A_1),\dots,X_{i_k}(A_k)\bigr) = \lambda \sum_{D' \supseteq \bar D} p_{D'} \int_{\mathbb{R}} P\bigl(t\mathbf{1} + Y_{\bar D} \in A_1\times\cdots\times A_k \,\big|\, Y\sim Q_{D'}\bigr)\,dt.$$

If every $Q_D$ has a density $q_D$, and $q_{D'}^{\bar D}$ denotes the joint marginal density of the coordinates in $\bar D$, the $k$-th order cross-cumulant density is

$$\kappa^X_{i_1\cdots i_k}(\tau_1,\dots,\tau_{k-1}) = \lambda \sum_{D'\supseteq \bar D} p_{D'} \int_{\mathbb{R}} q_{D'}^{\bar D}(t, t+\tau_1,\dots,t+\tau_{k-1})\,dt,$$

that is, a sum over markings containing $\bar D$ of the marking rate $\lambda p_{D'}$ times the density of the relative shifts $(Y_{i_2}-Y_{i_1},\dots,Y_{i_k}-Y_{i_1})$ under $Q_{D'}$.

**Second order.** For $i\ne j$, the covariance density is $\kappa^X_{ij}(\tau) = \lambda\sum_{D'\ni i,j} p_{D'}\, f^{D'}_{ij}(\tau)$ with $f^{D'}_{ij}$ the density of $Y_j - Y_i$ under $Q_{D'}$. When the two shifts are independent with common density $f$, this reduces to $\lambda\bar p_{\{i,j\}}\int f(t)f(t+\tau)\,dt$.

**Corollary.** For the multiple interaction process (no shifts, retention probability $\epsilon$), every cross-cumulant density of order $k$ among distinct neurons is $\lambda\epsilon^k$ times a Dirac delta at the origin of $\mathbb{R}^{k-1}$.

## Expansion

Decompose the mother process by marking and shift into independent Poisson processes. For the indices in $\bar D$, group the contributions into independent Poisson variables $\zeta_D$, $D \subseteq \bar D$, where $\zeta_D$ counts mother events whose marking contains $D$ but no other index of $\bar D$ and whose shifted copies fall in the relevant $A_i$. Then $X_{i_r}(A_r) \overset{d}{=} \sum_{D:\, i_r\in D\subseteq\bar D}\zeta_D$. By multilinearity of joint cumulants and independence of the $\zeta_D$, the only term surviving in $\kappa(X_{i_1}(A_1),\dots,X_{i_k}(A_k))$ is the $k$-th cumulant of $\zeta_{\bar D}$, which equals its mean because all cumulants of a Poisson variable equal its mean. Computing that mean by Campbell's formula gives the first display; letting the $A_r$ shrink to small intervals at $0,\tau_1,\dots,\tau_{k-1}$ and dividing by their lengths gives the density form. Because cumulants of order $k$ only see markings that contain all $k$ indices, structure in strictly lower-order markings (for example jittered pairs) leaves third and higher cumulants unchanged, unlike central moments.

## Depends on

- [GTaS model and its marginal Poisson structure](gtas-model-and-marginal-poisson-structure.md)

## Sources

- J. Trousdale, Y. Hu, E. Shea-Brown, K. Josić, "A generative spike train model with time-structured higher order correlations", Frontiers in Computational Neuroscience 7 (2013) 84, Theorem 1.1 (Equations 17–18), Equations 11–16, <https://doi.org/10.3389/fncom.2013.00084>, PMCID PMC3727174.
