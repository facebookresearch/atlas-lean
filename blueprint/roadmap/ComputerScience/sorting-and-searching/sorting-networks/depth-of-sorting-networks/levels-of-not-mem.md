# Comparators inside a block leave levels outside it unchanged

Let $ps$ be a list of
comparators all of whose wires lie in $[a, b)$. Then for all initial levels
$\ell : \mathbb{N} \to \mathbb{N}$ and every wire $x$ with $x < a$ or $b \le x$, the level of $x$
after $ps$ starting from $\ell$ is $\ell(x)$.
