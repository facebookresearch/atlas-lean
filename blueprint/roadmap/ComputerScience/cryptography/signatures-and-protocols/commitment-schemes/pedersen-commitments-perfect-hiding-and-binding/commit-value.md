# Pedersen commitment value

In a commutative group $G$ with public elements $g$ and $h$, the Pedersen commitment value of a message
$m \in \mathbb{Z}/q$ with opening $r \in \mathbb{Z}/q$ is $g^m h^r$ (Pedersen 1991). Here, for $u \in G$
and $a \in \mathbb{Z}/q$, $u^a$ means $u^{\bar a}$, where $\bar a$ is the representative of $a$ in
$\{0, \dots, q - 1\}$ (and $\bar a = |a|$ when $q = 0$, so that $\mathbb{Z}/q = \mathbb{Z}$); no
condition on the orders of $g$ and $h$ is assumed.
