# Correctness of distinguished-point evaluation of an iterate

Let $f : \alpha \to \alpha$, $K \le T$, and let $H \subseteq \alpha$ be a set of distinguished points such that every orbit segment of $K + 1$ pairwise distinct states meets $H$. Suppose a table stores $z(h) = f^{T - K}(h)$ for $h \in H$ and residues $R(l) = (T - K) \bmod l$ for $1 \le l \le K$. The procedure: walk $K$ steps from $x$, recording the first distinguished point $c = f^d(x)$ with $d \le K$ if any, and ending at $u = f^K(x)$; if $c$ exists output $f^{K - d}(z(c))$; otherwise the first $K + 1$ states repeat, so find the period $l \le K$ of $u$ and output $f^{R(l)}(u)$. For every input $x$ the output is $f^T(x)$.

## Proof sketch

If $c = f^d(x)$ is distinguished then $f^{K-d}(f^{T-K}(f^d(x))) = f^T(x)$ by composing iterates. Otherwise the hypothesis forces a repeat among $x, \dots, f^K(x)$, so $u = f^K(x)$ is periodic with some period $l \le K$, and $f^{T - K}(u) = f^{(T-K) \bmod l}(u)$.

## Depends on

- [Functional graphs: transient depth, cycles and canonical cycle representatives](functional-graph-transient-depth-and-cycles.md)

## Proof depends on

- [First hitting times and visit schedules in finite functional graphs](functional-graph-first-hitting-times.md)

## Sources

- P. C. van Oorschot, M. J. Wiener, "Parallel Collision Search with Cryptanalytic Applications", Journal of Cryptology, 1999.
