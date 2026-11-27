# Eventually periodic sex sequences are unavoidable in infinite pedigrees

An **infinite $n$-gendered population** (pedigree) is a directed graph $G = (V,E)$, with an edge $(v,u)$ meaning "$v$ is a parent of $u$", together with birthdates $t : V \to \mathbb R$ and edge genders $g : E \to \{1,\dots,n\}$, such that:

1. there are finitely many parentless vertices (roots);
2. each vertex has finitely many children;
3. for each $r \in \mathbb R$ only finitely many vertices have $t(v) \le r$, and $t(u) < t(v)$ for every edge $(u,v)$;
4. $|V| = \infty$;
5. every non-root $u$ has, for each $i \in \{1,\dots,n\}$, a parent $v$ with $g(v,u) = i$.

(For $n = 2$: every individual other than the founders has a mother and a father.) A sequence $s = (s_1, s_2, \dots) \in \{1,\dots,n\}^{\mathbb N}$ is **realized** in $G$ if there is an infinite descending line $v_1, v_2, \dots$ with $v_i$ a parent of $v_{i+1}$ and $g(v_i,v_{i+1}) = s_i$; it is **biologically unavoidable** if every infinite $n$-gendered population realizes it.

**Theorem.** Every eventually periodic sequence is biologically unavoidable. Moreover, in any such population there is an ancestrally closed set $V_0 \subseteq V$ such that every eventually periodic $s$ is realized by a line lying in $V_0$ along which every vertex of $V_0$ has a descendant.

**Theorem (avoidable sequences exist).** There is a sequence $s \in \{M,F\}^{\mathbb N}$ that is biologically avoidable; one can even choose $s$ so that no sex occurs three times in a row.

For $n = 1$ the first theorem is König's lemma: a finitely branching infinite tree with finitely many roots has an infinite path. For instance, every infinite pedigree with finitely many founders contains an infinite purely paternal line, an infinite purely maternal line and an infinite line alternating father, mother, father, ...

## Expansion

Let $V_i$ be the vertices reachable from a root by a path of length at most $i$; each $V_i$ is finite. For a sequence $s$ of period $p$ and a vertex $u \notin V_{p-1}$, walk backwards from $u$ choosing at each step the parent of the gender dictated by $s$ (read in reverse), stopping on entering $V_{p-1}$; this gives a finite path $s^*u$ ending at $u$ whose gender labels follow $s$ from a vertex of $V_{p-1}$. Infinitely many such paths start in the finite set $V_{p-1}$ and, by periodicity, can be aligned so that a König-type compactness argument extracts an infinite descending line realizing $s$. An eventually periodic sequence is handled by first following its finite prefix from a vertex that has infinitely many descendants realizing the periodic tail. Avoidable sequences are built against the explicit populations $T_h$ with $h(n)$ males and $h(n)$ females in generation $n$: when $h \to \infty$, long blocks $M^e F$ with suitably chosen $e$ cannot be realized at any fixed height.

## Sources

- Samuel Alexander, "Biologically Unavoidable Sequences", *Electronic Journal of Combinatorics* 20 (2013), P31, <https://doi.org/10.37236/3035>; preprint arXiv:1212.0186, <https://doi.org/10.48550/arXiv.1212.0186>. Numbering of the arXiv version: Section 1 (Definitions 1–2), Section 2 (Lemma 2, Definition 4, Proposition 5, Theorem 6, Corollary 7), Section 3 (Definition 6, Proposition 11, Corollary 12), Section 4 (the corollary on blocks of length at most 2).
