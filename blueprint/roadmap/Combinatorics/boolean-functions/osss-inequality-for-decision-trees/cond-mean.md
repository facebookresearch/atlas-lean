# Averaging out one coordinate

For a set $E$, weights $\nu = (\nu_e)_{e \in E}$ with $\nu_e : \{0, 1\} \to \mathbb{R}$, $e \in E$ and $g : \{0, 1\}^E \to \mathbb{R}$, the average of $g$ over the coordinate $e$ is the function

$$\mathbb{E}_\nu[g \mid \omega_{\ne e}](\omega) = \nu_e(1)\, g(\omega^{e \to 1}) + \nu_e(0)\, g(\omega^{e \to 0}),$$

where $\omega^{e \to b}$ agrees with $\omega$ except that its coordinate $e$ is $b$. When $E$ is finite and every $\nu_e$ is a probability weight ($\nu_e(0), \nu_e(1) \ge 0$ and $\nu_e(0) + \nu_e(1) = 1$), this is the conditional expectation of $g$ given the coordinates other than $e$ under the product measure; for general weights it is only this weighted sum (for instance $\nu_e(0) = \nu_e(1) = 1$ and $g = 1$ give $2$).
