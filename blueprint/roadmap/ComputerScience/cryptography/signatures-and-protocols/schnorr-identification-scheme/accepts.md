# Schnorr verifier's acceptance condition

Let $G$ be a commutative group, $q$ a natural
number and $g, y \in G$ (the base and the public key); for $h \in G$ and $a \in \mathbb{Z}/q$
write $h^a$ for $h^{\bar a}$, where $\bar a$ is the representative of $a$ in
$\{0, \dots, q - 1\}$ (and $\bar a = |a|$ when $q = 0$, so that $\mathbb{Z}/q = \mathbb{Z}$).
The verifier accepts a transcript $(I, r, s)$ with $I \in G$ and $r, s \in \mathbb{Z}/q$ when
$g^s (y^r)^{-1} = I$.
