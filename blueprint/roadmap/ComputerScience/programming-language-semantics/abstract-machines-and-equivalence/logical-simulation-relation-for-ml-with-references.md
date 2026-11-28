# Logical simulation relation for ML with references

Call finite sets $w$ of locations *worlds*; let $\mathrm{St}(w)$ be the states with domain $w$, $\mathrm{Prog}_{ty}(w)$ the programs of type $ty$ whose locations lie in $w$, and
$\mathrm{Rel}(w_1, w_2)$ the non-empty relations between $\mathrm{St}(w_1)$ and $\mathrm{St}(w_2)$. For $r \in \mathrm{Rel}(w_1, w_2)$ and $r' \in \mathrm{Rel}(w_1', w_2')$ on disjoint worlds, the smash product
$r \otimes r'$ relates the unions of related states; $r'' \rhd r$ ($r''$ *extends* $r$) if $r'' = r \otimes r'$ for some $r'$.

**Theorem.** For each $r \in \mathrm{Rel}(w_1, w_2)$ there are relations $e_1 \le_r e_2 : ty$ between $\mathrm{Prog}_{ty}(w_1)$ and $\mathrm{Prog}_{ty}(w_2)$ such that:

1. (simulation) $e_1 \le_r e_2 : ty$ holds if whenever $(s_1, s_2) \in r$ (so $s_i \in \mathrm{St}(w_i)$ covers the locations of $e_i$) and $s_1, e_1 \Rightarrow v_1, s_1'$, there are $r' \rhd r$ and $v_2, s_2'$ with $s_2, e_2 \Rightarrow v_2, s_2'$,
   $v_1 \le_{r'} v_2 : ty$ and $(s_1', s_2') \in r'$;
2. (extensionality on canonical forms) at $\mathrm{bool}$, $\mathrm{int}$ and $\mathrm{unit}$, $v_1 \le_r v_2$ iff $v_1 = v_2$; at $\mathrm{int\ ref}$, iff $!v_1 \le_r !v_2 : \mathrm{int}$ and
   $(v_1 := n) \le_r (v_2 := n) : \mathrm{unit}$ for all $n$; at $ty_1 * ty_2$, iff $\mathrm{fst}\, v_1 \le_r \mathrm{fst}\, v_2 : ty_1$ and $\mathrm{snd}\, v_1 \le_r \mathrm{snd}\, v_2 : ty_2$; and at $ty_1 \to ty_2$, iff for all $r' \rhd r$ and $v_1' \le_{r'} v_2' : ty_1$,
   $v_1\, v_1' \le_{r'} v_2\, v_2' : ty_2$;
3. (contextual preorder) for $e_1, e_2 \in \mathrm{Prog}_{ty}(w)$, $e_1 \le_{ctx} e_2 : ty$ iff $e_1 \le_{\mathrm{id}_w} e_2 : ty$, where $\mathrm{id}_w$ is the identity relation on $\mathrm{St}(w)$.

So local-state invariants, expressed as state relations, prove [contextual equivalences](contextual-preorder-for-ml-with-references.md) such as that of the two counters.

## Depends on

- [Contextual preorder for ML with references](contextual-preorder-for-ml-with-references.md)

## Proof depends on

- [Frame-stack termination for ML](frame-stack-termination-for-ml.md)
- [The unwinding theorem for recursive functions in ML](unwinding-theorem-for-ml.md)

## Sources

- A. M. Pitts, "Operational semantics and program equivalence", in G. Barthe, P. Dybjer, L. Pinto and J. Saraiva (eds.), *Applied Semantics*, LNCS 2395, Springer, 2002, 378–412, <https://doi.org/10.1007/3-540-45699-6_8>: Section 5, Definition 5.1 (state-relations), Theorem 5.2 with the proof of $p =_{ctx} m$ after it, and the construction of $\le_r$ through frame-stack relations (definitions (12)–(20)) with the proof sketch of Theorem 5.2.
