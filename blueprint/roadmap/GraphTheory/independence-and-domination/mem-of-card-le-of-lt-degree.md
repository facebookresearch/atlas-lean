# High-degree vertices lie in every small vertex cover

Let $G$ be a simple graph on a finite vertex set $V$, let $C \subseteq V$ be a vertex cover of $G$ (every edge has an endpoint in $C$), and let $k$ be a natural number with $|C| \le k$. Every vertex $v$ with $\deg_G(v) > k$ belongs to $C$.

This is the observation behind the high-degree reduction rule in the kernelization of vertex cover: a cover omitting $v$ must contain all $\deg_G(v)$ neighbors of $v$.

## Sources

- M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk, S. Saurabh, *Parameterized Algorithms*, Springer, 2015, Chapter 2.
