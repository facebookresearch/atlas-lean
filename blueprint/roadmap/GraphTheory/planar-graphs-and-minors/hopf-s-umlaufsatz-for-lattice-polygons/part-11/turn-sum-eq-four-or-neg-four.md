# Umlaufsatz for simple closed lattice walks

Let $n \ge 1$ and let $d = (d_0, \dots, d_{n-1})$ be a cyclic sequence of directions $d_i \in \mathbb{Z}/4\mathbb{Z}$, indices taken modulo $n$. Direction $k$ is the unit step $s(k)$, with $s(0) = (1, 0)$ (east), $s(1) = (0, 1)$ (north), $s(2) = (-1, 0)$ (west), $s(3) = (0, -1)$ (south), and the walk with step directions $d$ has vertices $p_k = \sum_{0 \le i < k} s(d_i)$ for $k = 0, \dots, n-1$ (so $p_0 = 0$; vertex indices are also taken modulo $n$). For directions $\mu, \nu$ let $\tau(\mu, \nu)$ be $1$ if $\nu = \mu + 1$ (left turn), $-1$ if $\nu = \mu + 3$ (right turn), and $0$ if $\nu = \mu$ or $\nu = \mu + 2$. Suppose the walk is closed, $\sum_{i} s(d_i) = 0$, its vertices are pairwise distinct, $n \ge 3$, and there are no U-turns: $d_{i+1} \neq d_i + 2$ for every $i$. Then

$$\sum_{i \in \mathbb{Z}/n\mathbb{Z}} \tau(d_i, d_{i+1}) \in \{4, -4\},$$

that is, the total turning is $\pm 4$ quarter turns and the rotation index is $\pm 1$.

## Sources

- Heinz Hopf, *Über die Drehung der Tangenten und Sehnen ebener Kurven*, Compositio Mathematica 2 (1935), 50–62, https://www.numdam.org/item/CM_1935__2__50_0.pdf, §2 (pp. 53–55) and §4 (pp. 58–61, curves with corners): the theorem of turning tangents, of which the statement for lattice walks is a specialisation.
