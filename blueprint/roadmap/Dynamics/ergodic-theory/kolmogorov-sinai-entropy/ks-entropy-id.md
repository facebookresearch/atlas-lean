# The identity has zero entropy

For every probability space $(X, \mu)$, the identity map has Kolmogorov–Sinai entropy $h_\mu(\mathrm{id}) = 0$.

Under the identity, the dynamical refinement $\xi \vee \xi \vee \dots \vee \xi$ of a finite measurable partition
[has the same entropy as $\xi$](partition-entropy-iterate-join-id.md): a word $(i, \dots, i)$ gives back the atom
$C_i$, and any other word gives a subset of the intersection of two distinct atoms, a null set. So
$\frac1n H(\xi \vee \dots \vee \xi) = \frac1n H(\xi) \to 0$. By [invariance under isomorphism modulo null sets](ks-entropy-eq-of-is-isomorphic-mod0.md)
every measure-preserving system isomorphic to the identity also has entropy $0$; at the other extreme, Bernoulli shifts have
[positive entropy](of-real-le-ks-entropy-shift.md). Entropy zero is far from triviality, though:
[irrational rotations](ks-entropy-add-circle-rotation-eq-zero.md) are ergodic and also have entropy zero.

## Sources

- Ya. G. Sinai, *Kolmogorov–Sinai entropy*, Scholarpedia 4(3):2034 (2009), §Definition and §History (entropy
  was expected to vanish for "deterministic" systems and to be positive for "probabilistic" ones).
