# Entropy of a function under a product weight

Let $E$ be a finite set, $\nu = (\nu_e)_{e \in E}$ a family of weights $\nu_e : \{0, 1\} \to \mathbb{R}$, and $\mathbb{E}_\nu[g] = \sum_{\omega} \prod_{e} \nu_e(\omega_e)\, g(\omega)$ the corresponding [expectation](../../osss-inequality-for-decision-trees/expect.md). The entropy of $g : \{0, 1\}^E \to \mathbb{R}$ is

$$\mathrm{Ent}_\nu(g) = \mathbb{E}_\nu[\Phi(g)] - \Phi(\mathbb{E}_\nu[g]), \qquad \Phi(x) = x \log x,$$

where [$\Phi$](esd-phi.md) uses the logarithm extended by $\log 0 = 0$ and $\log x = \log \lvert x\rvert$ for $x < 0$; in particular $\Phi(0) = 0$.
