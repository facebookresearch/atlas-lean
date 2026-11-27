# Zmod parity add

For all Booleans $a, b, c$, writing $[\varphi] \in \mathbb{Z}/2\mathbb{Z}$ for $1$ if $\varphi$ holds and $0$ otherwise, the identity

$$
[a \wedge (b \oplus c)] = [a \wedge b] + [a \wedge c]
$$

holds in $\mathbb{Z}/2\mathbb{Z}$. The modulus is essential: when $a$, $b$, $c$ are all true the left side is $0$ and the right side is $1 + 1$, which is $0$ in $\mathbb{Z}/2\mathbb{Z}$ but $2$ in $\mathbb{Z}$.
