# Subtree step of the OSSS induction

Let $E$ be a finite set, $\nu$ a [product probability weight](is-prob-weight.md) on $\{0, 1\}^E$, $e \in E$, $t$ and $f$ [decision trees](decision-tree.md) on $E$, and $G : \{0, 1\}^E \to \mathbb{R}$ with $G(\omega^{\oplus e}) = G(\omega)$ for every $\omega$, where $\omega^{\oplus e}$ is $\omega$ with coordinate $e$ flipped. Let $T$ be the tree that queries $e$ and continues with $t$ if $\omega_e = 1$ and with $f$ if $\omega_e = 0$, and write $f_T$ for the $0/1$-valued function computed by $T$. Then

$$\mathrm{Cov}_\nu(f_T, G) = \nu_e(1)\, \mathrm{Cov}_{\nu^{e,1}}(f_t, G) + \nu_e(0)\, \mathrm{Cov}_{\nu^{e,0}}(f_f, G),$$

where $\nu^{e,b}$ is $\nu$ with the weight at $e$ replaced by the [point mass](pt.md) at $b$. This is the subtree step of the induction proving the OSSS inequality.
