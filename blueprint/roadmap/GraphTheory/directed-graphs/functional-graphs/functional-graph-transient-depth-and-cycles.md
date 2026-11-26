# Functional graphs: transient depth, cycles and canonical cycle representatives

The functional graph of a map $f : \alpha \to \alpha$ on a finite set has an arc $x \to f(x)$ from every state. Every orbit $x, f(x), f^2(x), \dots$ is eventually periodic: its transient depth $\mu(x)$ is the least $j$ such that $f^j(x)$ is a periodic point, and its eventual cycle $C(x)$ is the cycle containing $f^{\mu(x)}(x)$, of length $\lambda(x)$. For $i, j \ge \mu(x)$, $f^i(x) = f^j(x)$ exactly when $i \equiv j \pmod{\lambda(x)}$. Given a linear order on $\alpha$, the canonical representative of $C(x)$ is its least element, the canonical time is the first visit to it, and the phase of a periodic state is its position on the cycle relative to the representative. The map's maximal transient depth is $\mu_f = \max_x \mu(x)$ and its cycle period $\lambda_f$ is the least common multiple of all cycle lengths.

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 2: Seminumerical Algorithms", Addison-Wesley, 1997.
