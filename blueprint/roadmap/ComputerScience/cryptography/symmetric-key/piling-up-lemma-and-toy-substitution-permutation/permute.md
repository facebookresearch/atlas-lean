# Permute

Let $m \in \mathbb{N}$, $\pi$ a permutation of $\{0, \dots, m-1\}$ and $z \in \mathrm{Bool}^m$. Permuting the coordinates of $z$ by $\pi$ gives

$$
\mathrm{permute}(\pi, z)_i = z_{\pi(i)},
$$

that is, $z \circ \pi$. At $E = F = \{0, \dots, m-1\}$ this is the forward map of the [configuration relabeling `cfgEquiv`](../../../../Probability/correlation-inequalities/harris-fkg-bk/van-den-berg-kesten-inequality/cfg-equiv.md) for $\pi$; its inverse is the [mask transport](transport-mask.md) $u \mapsto u \circ \pi^{-1}$.
