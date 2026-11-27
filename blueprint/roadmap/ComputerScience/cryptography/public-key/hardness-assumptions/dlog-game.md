# Discrete-logarithm experiment

Let $G$ be a commutative group, $g \in G$ and $q \ge 1$; for $u \in G$ and $a \in \mathbb{Z}/q$ write
$u^a$ for $u^{\bar a}$, where $\bar a$ is the representative of $a$ in $\{0, \dots, q - 1\}$. Let a
solver map an element of $G$ and coins in a finite nonempty set $S$ to an exponent in $\mathbb{Z}/q$.
The discrete-logarithm experiment (Katz and Lindell, Section 8.3.2) draws $x \in \mathbb{Z}/q$ and coins
$s$ uniformly, gives the solver $h = g^x$, and outputs $1$ when its output $x'$ satisfies $g^{x'} = h$.
