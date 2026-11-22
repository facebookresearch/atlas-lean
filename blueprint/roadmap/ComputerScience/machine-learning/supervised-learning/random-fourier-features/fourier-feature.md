# Random Fourier feature

For a frequency $\omega$ in a real inner product space $E$ (in the source, $\mathbb{R}^d$) and a phase $b \in \mathbb{R}$, the random Fourier feature of an input $x \in E$ is

$$
z_{\omega, b}(x) = \sqrt{2}\, \cos(\langle \omega, x\rangle + b).
$$

It projects $x$ on the line spanned by $\omega$ and passes the result through a shifted sinusoid; it takes values in $[-\sqrt2, \sqrt2]$.

## Sources

- A. Rahimi and B. Recht, *Random features for large-scale kernel machines*, Advances in Neural Information Processing Systems 20 (NIPS 2007); author PDF at <https://people.eecs.berkeley.edu/~brecht/papers/07.rah.rec.nips.pdf>, Section 3 (the real-valued mapping $z_\omega(x) = \sqrt{2} \cos(\omega' x + b)$ after equation (2)).
