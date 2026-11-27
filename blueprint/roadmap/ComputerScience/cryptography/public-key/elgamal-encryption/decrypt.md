# ElGamal decryption

Let $G$ be a commutative group and $q$ a natural number. For
$a \in \mathbb{Z}/q\mathbb{Z}$ and $c \in G$ write $c^a$ for $c^{\operatorname{val}(a)}$, where
$\operatorname{val}(a) \in \mathbb{N}$ is the representative of $a$ in $\{0, \dots, q-1\}$ if
$q \ge 1$ and $|a|$ if $q = 0$. Decrypting a ciphertext $(c_1, c_2) \in G \times G$ with the
secret key $x \in \mathbb{Z}/q\mathbb{Z}$ gives $c_2 \cdot (c_1^x)^{-1}$.
