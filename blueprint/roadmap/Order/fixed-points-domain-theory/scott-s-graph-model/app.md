# Application in the graph model

Every set $u \subseteq \mathbb{N}$ acts as a function on $P(\omega)$ by

$$\operatorname{app}(u, x) = \{m \mid \exists n,\ e_n \subseteq x \text{ and } \langle n, m\rangle \in u\}$$

(D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), 522–587, §1, definition of $\operatorname{fun}(u)(x)$; in the language LAMBDA of §2 this is the application $u(x)$).

## Background

- [Graph of a function on `P(ω)`](graph.md): the coding that application inverts.
- [Application in `P(ω)` is jointly Scott-continuous](scott-continuous-app.md): every $u$ determines a continuous function.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.
