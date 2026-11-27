# Transport Mask

Let $m \in \mathbb{N}$, $u \in \mathrm{Bool}^m$ a mask and $\pi$ a permutation of $\{0, \dots, m-1\}$. Transporting $u$ back across $\pi$ gives the mask with

$$
\mathrm{transportMask}(u, \pi)_i = u_{\pi^{-1}(i)} .
$$

It is the inverse of the coordinate [permutation](permute.md) $z \mapsto z \circ \pi$: at $E = F = \{0, \dots, m-1\}$, the inverse map of the [configuration relabeling `cfgEquiv`](../../../../Probability/correlation-inequalities/harris-fkg-bk/van-den-berg-kesten-inequality/cfg-equiv.md) for $\pi$ is $u \mapsto u \circ \pi^{-1}$. The trail argument uses this orientation, since the parity of a [permuted](permute.md) word under $u$ equals the parity of the unpermuted word under the transported mask.
