# Up-front versus fresh randomness

Let $X$ be finite and nonempty, $Y$ an additive commutative group and $f \colon X \to Y$. For every $n$ and every oracle computation $c$ that makes at most $n$ encryption queries along every path, draw $\rho$ uniformly from $X^n$, run $c$ with $\mathrm{runEnc}$ from index $0$ and discard the final index. The resulting distribution equals the output distribution of $c$ when each query $m$ is answered with fresh randomness, by $(r, f(r) + m)$ for $r$ uniform on $X$, mapped by `some`. In particular the bounded run never fails.

Here $\mathrm{runEnc}$ runs an oracle computation against the encryption oracle with up-front randomness $\rho \in X^q$, starting from a query index $i$: a returned value $a$ gives `some` $(a, i)$; a query $m$ with $i < q$ is answered by $(\rho_i, f(\rho_i) + m)$ and the run continues from index $i + 1$; a query with $i \ge q$ makes the run fail (`none`).
