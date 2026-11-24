# ElGamal encryption

Let $G$ be a commutative group with a fixed element $g$ and let $q$ be
a natural number. The ElGamal encryption of a message $m \in G$ under the public key $h \in G$
with randomness $y \in \mathbb{Z}/q$ is the pair $(g^y, h^y m) \in G \times G$. Here a power
$k^a$ with $k \in G$ and $a \in \mathbb{Z}/q$ means $k^{v(a)}$, where $v(a) \in \{0, \dots, q - 1\}$
is the least nonnegative representative of $a$ if $q \ge 1$, and $v(a) = |a|$ if $q = 0$ (when
$\mathbb{Z}/0 = \mathbb{Z}$).
