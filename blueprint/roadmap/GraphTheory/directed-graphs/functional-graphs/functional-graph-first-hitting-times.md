# First hitting times and visit schedules in finite functional graphs

Let $f : \alpha \to \alpha$ with $\alpha$ finite and $x, y \in \alpha$. If $y = f^t(x)$ for some $t$, then the first such time $\tau(x, y)$ is less than $|\alpha|$ and is given in closed form: if $y$ is periodic, it is reached exactly when $C(x) = C(y)$, first at the transient depth of $x$ plus the phase difference of $f^{\mu(x)}(x)$ and $y$ on the common cycle; if $y$ is transient, it is reached only at time $\mu(x) - \mu(y)$. After the first visit, the visits to $y$ form an arithmetic progression with step the minimal period of $y$ (a single visit when $y$ is not periodic). Two orbits meet at a common time if and only if $f^{|\alpha|}(x) = f^{|\alpha|}(x')$.

## Proof sketch

Past the transient, states correspond to phases modulo the cycle length, and iterating shifts the phase by one. A periodic target is therefore hit when the phase of the orbit first equals its phase; a transient target lies on the unique tail path, which the orbit can cross only once. Since the tail plus the cycle has at most $|\alpha|$ states, the first visit occurs before time $|\alpha|$.

## Depends on

- [Functional graphs: transient depth, cycles and canonical cycle representatives](functional-graph-transient-depth-and-cycles.md)

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 2: Seminumerical Algorithms", Addison-Wesley, 1997.
