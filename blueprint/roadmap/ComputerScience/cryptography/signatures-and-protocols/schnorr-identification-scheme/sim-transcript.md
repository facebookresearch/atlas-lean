# Simulated Schnorr transcript

Let $G$ be a commutative group, $q \ge 1$ and $g, y \in G$;
for $h \in G$ and $a \in \mathbb{Z}/q$ write $h^a$ for $h^{\bar a}$, where
$\bar a \in \{0, \dots, q - 1\}$ is the representative of $a$. For a challenge $r$ and an answer
$s$ in $\mathbb{Z}/q$, the simulated transcript is the element $(g^s (y^r)^{-1}, r, s)$ of
$G \times \mathbb{Z}/q \times \mathbb{Z}/q$.
