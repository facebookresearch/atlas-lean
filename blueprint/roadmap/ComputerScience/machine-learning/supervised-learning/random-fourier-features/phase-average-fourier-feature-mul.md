# Averaging a random Fourier feature over the phase

For every frequency $\omega$ and inputs $x, y$,

$$
\frac{1}{2\pi} \int_0^{2\pi} z_{\omega, b}(x)\, z_{\omega, b}(y)\, db = \cos \langle \omega, x - y\rangle .
$$

Proof: by the sum of angles formula, $2 \cos u \cos v = \cos(u - v) + \cos(u + v)$; with $u = \langle\omega, x\rangle + b$ and $v = \langle\omega, y\rangle + b$, the first term is $\cos\langle\omega, x - y\rangle$, independent of $b$, and the second, $\cos(2b + \langle\omega, x + y\rangle)$, integrates to $0$ over a period.

## Sources

- A. Rahimi and B. Recht, *Random features for large-scale kernel machines*, Advances in Neural Information Processing Systems 20 (NIPS 2007); author PDF at <https://people.eecs.berkeley.edu/~brecht/papers/07.rah.rec.nips.pdf>, Section 3 ("a consequence of the sum of angles formula").
