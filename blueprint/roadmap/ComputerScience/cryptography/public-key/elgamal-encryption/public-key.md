# ElGamal public key

Let $G$ be a commutative group with a fixed element $g$ and let $q$ be
a natural number. The public key of a secret key $x \in \mathbb{Z}/q$ is $h = g^{v(x)} \in G$,
where $v(x) \in \{0, \dots, q - 1\}$ is the least nonnegative representative of $x$ if $q \ge 1$,
and $v(x) = |x|$ if $q = 0$ (when $\mathbb{Z}/0 = \mathbb{Z}$).
