# Transcript of Diffie–Hellman key agreement

For a commutative group $G$, an element $g \in G$, a natural number $q$ and secrets
$a, b \in \mathbb{Z}/q$, the transcript of Diffie–Hellman key agreement (Katz and Lindell,
Construction 10.2) is the pair $(g^a, g^b)$ of Alice's and Bob's messages. Here, for $u \in G$ and
$a \in \mathbb{Z}/q$, $u^a$ means $u^{\bar a}$, where $\bar a$ is the representative of $a$ in
$\{0, \dots, q - 1\}$ (and $\bar a = |a|$ when $q = 0$, so that $\mathbb{Z}/q = \mathbb{Z}$); no
condition on the order of $g$ is assumed.
