# Honest Schnorr transcript

Let $G$ be a commutative group, $q \ge 1$ and $g \in G$; for
$a \in \mathbb{Z}/q$ write $g^a$ for $g^{\bar a}$, where $\bar a \in \{0, \dots, q - 1\}$ is the
representative of $a$. For a secret key $x$, prover randomness $k$ and challenge $r$, all in
$\mathbb{Z}/q$, the honest transcript is the element $(g^k, r, rx + k)$ of
$G \times \mathbb{Z}/q \times \mathbb{Z}/q$.
