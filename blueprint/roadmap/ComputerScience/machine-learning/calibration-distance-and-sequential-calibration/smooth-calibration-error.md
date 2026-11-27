# Smooth calibration error and interval calibration error

For a distribution $\Gamma$ of pairs $(v, y) \in [0,1] \times \{0,1\}$, the **smooth calibration error** is

$$
\mathrm{smCE}(\Gamma) = \sup_{w} \mathbb{E}_{(v,y) \sim \Gamma}\big[w(v)\,(y - v)\big],
$$

the supremum over all $1$-Lipschitz functions $w : [0,1] \to [-1,1]$. The **interval calibration error** is $\mathrm{intCE}(\Gamma)=\inf_{\mathcal{I}}\Big(\sum_{I\in\mathcal{I}}\big|\mathbb{E}_{(v,y)\sim\Gamma}[(y-v)\mathbf{1}[v\in I]]\big|+\sum_{I\in\mathcal{I}}|I|\,\Pr_{\Gamma}[v\in I]\Big)$, the infimum over partitions $\mathcal{I}$ of $[0,1]$ into finitely many intervals, where $|I|$ is the length of $I$. A calibration measure $\mu$, assigning a value $\mu_D(f)$ to each distribution $D$ over $X \times \{0,1\}$ and predictor $f$, is **$(c,s)$-consistent** if it satisfies robust completeness $\mu_D(f) \le a\,\mathrm{dCE}_D(f)^c$ and robust soundness $\mu_D(f) \ge b\,\mathrm{dCE}_D(f)^s$ for constants $a, b > 0$ and all $D$ and $f$, where $\mathrm{dCE}_D$ is the true distance to calibration; a measure of the law $\Gamma$ of $(f(x),y)$ is evaluated at $\Gamma$.

## Depends on

- [Distance to calibration and its upper and lower variants](distance-to-calibration.md)

## Sources

- J. Blasiok, P. Gopalan, L. Hu, P. Nakkiran, "A Unifying Theory of Distance from Calibration", STOC (2023), arXiv:2211.16886.
