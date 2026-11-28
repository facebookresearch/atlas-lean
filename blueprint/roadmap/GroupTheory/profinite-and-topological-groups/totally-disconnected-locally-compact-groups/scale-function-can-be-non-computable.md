# The scale function of a computably presented totally disconnected locally compact group can be non-computable

Some totally disconnected locally compact group has a computable presentation with a computable sequence of elements on which its scale function, which measures how conjugation stretches compact open subgroups, is not computable.

Let $G$ be a totally disconnected locally compact (t.d.l.c.) group. For $g \in G$ and a compact open subgroup $V$ of $G$ let $m(g, V) = |gVg^{-1} : V \cap gVg^{-1}|$; the *scale* of $g$ is $s(g) = \min_V m(g, V)$, the minimum over all compact open subgroups $V$, a positive integer (Willis). A subtree $T$ of the tree $\mathbb{N}^*$ of finite sequences of natural numbers is *computably locally compact* if it is computable, has no leaves, and for some $k \in \mathbb{N}$ there is a computable $H \colon \mathbb{N}^k \times \mathbb{N} \to \mathbb{N}$ with $\rho(i) \le H(\rho \restriction k, i)$ for every $\rho \in T$ of length greater than $k$ and every $i < |\rho|$. A *computable Baire presentation* of $G$ is a topological group $([T], \mathrm{Mult}, \mathrm{Inv})$ isomorphic to $G$, where $[T]$ is the space of infinite paths of a computably locally compact tree $T$ and $\mathrm{Mult} \colon [T] \times [T] \to [T]$ and $\mathrm{Inv} \colon [T] \to [T]$ are computable (by oracle Turing machines).

**Theorem (Melnikov and Nies, with Willis).** There are a computable Baire presentation $([T], \mathrm{Mult}, \mathrm{Inv})$ of a t.d.l.c. group $G$ and a computable sequence $(g_i)_{i \ge 1}$ of paths on $T$ such that the function $i \mapsto s(g_i)$ is not computable. Moreover, $G$ is elementary in the sense of Wesolek (Theorem 11.8 of arXiv:2204.09878v6).

In particular the scale function of $G$ is not computable for this presentation, although it is always computably approximable from above (Fact 8.8 of the source). The source leaves open whether some computably presented t.d.l.c. group has non-computable scale function for every one of its computable presentations. By contrast, the source shows that for computably presented t.d.l.c. groups the Haar measure and the modular function are computable, and so are Cayley–Abels graphs in the compactly generated case.

## Depends on

- [Group](../../group-basics/group.md)
- [Topological group](../../../Topology/topological-groups/topological-group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Let $H$ be the additive group of $\mathbb{F}_2((t))$. Willis gave automorphisms $\pi_t$ ($t \in \mathbb{N}$) and $\pi$ of $H$ with $\pi_t \to \pi$, $s(\pi_t) = 1$ and $s(\pi) = 2$. Uniformly in $i$, the proof builds the split extension $G_i = \mathbb{Z} \ltimes H$ for an automorphism $\hat\beta_i$ that follows $\pi$ while $i$ has not entered the halting set $K$ and switches to following $\pi_t$ if $i$ enters $K$ at stage $t$, so that the generator $g_i$ of $\mathbb{Z}$ has scale $2$ if $i \notin K$ and $1$ otherwise. The group $G$ is a computable local direct product of the $G_i$ over compact open subgroups $U_i$ (via Proposition 9.5), and computing $i \mapsto s(g_i)$ would decide $K$. A good expansion links Willis's example of a discontinuous scale function on $\mathrm{Aut}(H)$ and the computable presentation of local direct products.

## Sources

- A. Melnikov and A. Nies, "Computably totally disconnected locally compact groups", *The Journal of Symbolic Logic*, 2026, pp. 1–52, doi:10.1017/jsl.2026.10222; read as arXiv:2204.09878v6, <https://arxiv.org/abs/2204.09878v6>: Theorem 11.8 (Appendix 1, with George Willis) and its proof, Definition 2.4, Definition 7.1, Fact 8.8, the definition of the scale function and the summary of results in Section 1, in the numbering of arXiv:2204.09878v6.
