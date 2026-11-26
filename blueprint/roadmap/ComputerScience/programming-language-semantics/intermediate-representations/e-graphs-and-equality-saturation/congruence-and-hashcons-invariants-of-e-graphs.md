# Congruence and hashcons invariants of e-graphs

Let $(U, M, H)$ be an [e-graph](e-graphs.md). It defines three equivalence relations: on e-class ids, $a \equiv_{\mathrm{id}} b$ iff $\mathrm{find}(a) = \mathrm{find}(b)$; on e-nodes, $n_1 \equiv_{\mathrm{node}} n_2$ iff some $M[a]$ contains both; on terms, $t_1 \equiv_{\mathrm{term}} t_2$ iff some e-class represents both. One step of *congruence* relates $f(a_1, a_2, \dots) \cong f(b_1, b_2, \dots)$ iff $a_i \equiv_{\mathrm{id}} b_i$ for all $i$, and $\cong^*$ is the *congruence closure* of $\equiv_{\mathrm{node}}$, the least equivalence relation containing $\equiv_{\mathrm{node}}$ and $\cong$.

- **Congruence invariant.** $\equiv_{\mathrm{node}}$ equals $\cong^*$: congruent e-nodes lie in the same e-class, so in particular each e-node lies in a single e-class.
- **Hashcons invariant.** For all e-nodes $n$ and ids $a$, $n \in M[a]$ iff $H[\mathrm{canonicalize}(n)] = \mathrm{find}(a)$. Then $\mathrm{lookup}(n) = H[\mathrm{canonicalize}(n)]$ finds the e-class, if any, containing an e-node congruent to $n$.

The operation $\mathrm{add}(n)$ returns $\mathrm{lookup}(n)$ if it exists and otherwise creates a new e-class $\{n\}$; $\mathrm{merge}(a, b)$ unions $a$ and $b$ in $U$ and sets $M[a]$ and $M[b]$ to $M[a] \cup M[b]$. *E-matching* a pattern $p$ with variables returns the pairs $(\sigma, c)$ of a substitution of e-class ids for the variables and an e-class $c$ representing $p[\sigma]$. A rewrite $\ell \to r$ is applied by computing $\mathrm{merge}(c, \mathrm{add}(r[\sigma]))$ for every match $(\sigma, c)$ of $\ell$.

## Depends on

- [E-graphs](e-graphs.md)

## Sources

- M. Willsey, C. Nandi, Y. R. Wang, O. Flatt, Z. Tatlock and P. Panchekha, "egg: Fast and extensible equality saturation", arXiv:2004.03082, <https://arxiv.org/abs/2004.03082> (also *Proceedings of the ACM on Programming Languages* 5(POPL):23, 2021), Sections 2.1.2–2.1.3: Definitions 2.4 (equivalence), 2.5 (congruence), 2.6 (the congruence invariant) and 2.7 (the hashcons invariant), and the operations add, merge, find and ematch.
