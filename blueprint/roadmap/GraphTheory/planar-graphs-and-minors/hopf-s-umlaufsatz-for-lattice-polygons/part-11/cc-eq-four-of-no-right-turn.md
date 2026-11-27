# Discrete Umlaufsatz for lattice walks without right turns

Let $n \ge 1$ and let $d = (d_0, \dots, d_{n-1})$ be a cyclic sequence of directions $d_i \in \mathbb{Z}/4\mathbb{Z}$, indices taken modulo $n$. Direction $k$ is the unit step $s(k)$, with $s(0) = (1, 0)$ (east), $s(1) = (0, 1)$ (north), $s(2) = (-1, 0)$ (west), $s(3) = (0, -1)$ (south), and the walk with step directions $d$ has vertices $p_k = \sum_{0 \le i < k} s(d_i)$ for $k = 0, \dots, n-1$ (so $p_0 = 0$; vertex indices are also taken modulo $n$). If the walk is closed, $\sum_{i} s(d_i) = 0$, its vertices are pairwise distinct, and every turn $d_{i+1} - d_i$ is $0$ (straight) or $1$ (a left quarter turn), then exactly $4$ indices $i$ have $d_{i+1} - d_i = 1$: the direction makes exactly one full counterclockwise revolution. Right turns and reversals are excluded by hypothesis.

## Sources

- Heinz Hopf, *Über die Drehung der Tangenten und Sehnen ebener Kurven*, Compositio Mathematica 2 (1935), 50–62, https://www.numdam.org/item/CM_1935__2__50_0.pdf, §2 (pp. 53–55) and §4 (pp. 58–61, curves with corners): the theorem of turning tangents, of which the statement for lattice walks is a specialisation.
