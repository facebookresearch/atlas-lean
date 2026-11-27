# E-graphs

Fix a set of function symbols $f, g, \dots$, each with an arity. *Terms* are $f$ or $f(t_1, \dots, t_m)$ with $m \ge 1$. Let $e$-class ids $a, b, \dots$ be opaque identifiers compared only for equality. An *e-node* is $f$ or $f(a_1, \dots, a_m)$ with e-class ids as children, and an *e-class* is a nonempty finite set of e-nodes.

An *e-graph* is a triple $(U, M, H)$ where
- $U$ is a union-find structure storing an equivalence relation $\equiv_{\mathrm{id}}$ on e-class ids, with a function $\mathrm{find}$ such that $\mathrm{find}(a) = \mathrm{find}(b)$ iff $a \equiv_{\mathrm{id}} b$;
- the *e-class map* $M$ maps e-class ids to e-classes, with $a \equiv_{\mathrm{id}} b$ iff $M[a] = M[b]$; the id $a$ refers to the e-class $M[\mathrm{find}(a)]$;
- the *hashcons* $H$ maps e-nodes to e-class ids.

An e-class id $a$ is *canonical* if $\mathrm{find}(a) = a$, and an e-node is canonical if it equals $\mathrm{canonicalize}(f(a_1, a_2, \dots)) = f(\mathrm{find}(a_1), \mathrm{find}(a_2), \dots)$.

*Representation* is defined recursively: an e-graph represents a term if one of its e-classes does; an e-class represents a term if one of its e-nodes does; and an e-node $f(a_1, a_2, \dots)$ represents a term $f(t_1, t_2, \dots)$ if each e-class $M[a_i]$ represents $t_i$. An e-graph with cycles can represent infinitely many terms: the e-class $C = \{a, f(C)\}$ represents $a, f(a), f(f(a)), \dots$. A cycle without a way out represents nothing: the e-class $C = \{f(C)\}$ represents no term, by induction on the height of terms.

## Sources

- M. Willsey, C. Nandi, Y. R. Wang, O. Flatt, Z. Tatlock and P. Panchekha, "egg: Fast and extensible equality saturation", *Proceedings of the ACM on Programming Languages* 5(POPL), Article 23, 2021, doi:10.1145/3434304, author copy arXiv:2004.03082v3 <https://arxiv.org/abs/2004.03082>, Section 2.1.1: Figure 1 and Definitions 2.1 (e-graph), 2.2 (canonicalization) and 2.3 (representation of terms), and Figure 2.
