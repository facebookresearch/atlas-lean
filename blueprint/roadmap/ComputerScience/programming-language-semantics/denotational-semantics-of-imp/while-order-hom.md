# The while-loop functional as a monotone map

For a boolean guard $b$ and a relation $B$
between states (the body denotation), this is the map $\Phi$ on relations between states, ordered
by inclusion, where $\Phi(R)$ relates $s$ to $s'$ exactly when either $b$ is false in $s$ and
$s' = s$, or $b$ is true in $s$ and there is a state $m$ with $B(s, m)$ and $R(m, s')$. The map
$\Phi$ is monotone: $R_1 \subseteq R_2$ implies $\Phi(R_1) \subseteq \Phi(R_2)$.
