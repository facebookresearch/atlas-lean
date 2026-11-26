# Completeness of the Schnorr identification scheme

Let $G$ be a commutative group,
$q \ge 1$ a natural number and $g \in G$ with $g^q = 1$; for $h \in G$ and $a \in \mathbb{Z}/q$
write $h^a$ for $h^{\bar a}$, where $\bar a \in \{0, \dots, q - 1\}$ is the representative
of $a$. For all $x, k, r \in \mathbb{Z}/q$, with public key $y = g^x$, the honest transcript
$(g^k, r, rx + k)$ is accepted, that is, $g^{rx + k} (y^r)^{-1} = g^k$.
