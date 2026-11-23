# Russo's formula on a single fiber

Let $E$ be a finite set, $p \in \mathbb{R}$, $A \subseteq \{0,1\}^E$ an increasing event and $e \in E$. Let $\omega_1, \omega_0 \in \{0,1\}^E$ be the two configurations of one fiber of $e$: $\omega_1(e) = 1$, $\omega_0(e) = 0$, $\omega_1^{e,1} = \omega_1$, $\omega_1^{e,0} = \omega_0$, and $W_p^{(e)}(\omega_1) = W_p^{(e)}(\omega_0)$. Then

$$\mathbf{1}_A(\omega_1)\,W_p^{(e)}(\omega_1) - \mathbf{1}_A(\omega_0)\,W_p^{(e)}(\omega_0) = \mathbf{1}_{\mathrm{Piv}_e(A)}(\omega_1)\,W_p(\omega_1) + \mathbf{1}_{\mathrm{Piv}_e(A)}(\omega_0)\,W_p(\omega_0),$$

where $\mathrm{Piv}_e(A)$ is the set of configurations at which $e$ is pivotal for $A$, $W_p$ is the [product weight](config-weight.md) and $W_p^{(e)}$ the [weight off $e$](weight-off.md).
