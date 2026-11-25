# Step-indexed safety for concurrent separation logic

Fix a parallel heap language with a small-step reduction relation $c/h \to c'/h'$ on pairs of a command and a heap,
an error judgement $c/h \to \mathrm{err}$, atomic blocks $\mathbf{atomic}\ c$ and parallel composition $c_1 \parallel c_2$. Heaps are
finite partial maps from locations to values, $h_1 \uplus h_2$ denotes the union of heaps with disjoint domains, and a
command is *final* when it is a value $v$. The error judgement covers access to an unallocated location and data
races: $(c_1 \parallel c_2)/h \to \mathrm{err}$ when the locations accessed by the next steps of $c_1$ and of $c_2$ intersect, where an
atomic block counts as accessing no location. Let $J$ (the shared-memory invariant) be a predicate on heaps, and let $Q$
be a postcondition, a predicate on a result value and a heap.

$\mathrm{Safe}_n(c, h, Q)$ is defined by induction on $n$:

- $\mathrm{Safe}_0(c, h, Q)$ always holds;
- if $c$ is a value $v$, then $\mathrm{Safe}_{n+1}(c, h, Q)$ holds iff $Q\,v\,h$;
- otherwise $\mathrm{Safe}_{n+1}(c, h, Q)$ holds iff for all heaps $h_j$ and $h_f$ with $J\,h_j$ and $h \uplus h_j \uplus h_f$ defined,
  $c/(h \uplus h_j \uplus h_f) \not\to \mathrm{err}$, and every reduction $c/(h \uplus h_j \uplus h_f) \to c'/h'$ has
  $h' = h_1' \uplus h_j' \uplus h_f$ for some $h_1'$, $h_j'$ with $J\,h_j'$ and $\mathrm{Safe}_n(c', h_1', Q)$.

The semantic triple $J \models \{P\}\,c\,\{Q\}$ holds when $\mathrm{Safe}_n(c, h, Q)$ for every $n$ and every heap $h$ with $P\,h$. For the
reduction rules of the language this triple validates the frame rule (from $J \models \{P\}\,c\,\{Q\}$ infer
$J \models \{P \ast R\}\,c\,\{\lambda v.\, Q\,v \ast R\}$) and the parallel rule (from $J \models \{P_1\}\,c_1\,\{\lambda\_.\,Q_1\}$ and
$J \models \{P_2\}\,c_2\,\{\lambda\_.\,Q_2\}$ infer $J \models \{P_1 \ast P_2\}\,c_1 \parallel c_2\,\{\lambda\_.\,Q_1 \ast Q_2\}$), where $\ast$ is separating
conjunction. In particular a command satisfying such a triple has no data race between non-atomic accesses.

## Depends on

- [Frame rule](../separation-logic/frame.md)

## Expansion

Fix the concrete command language and its reduction and error rules, including the race rule above, and state the
frame-property lemmas for single steps that the two validity proofs use.

## Sources

- X. Leroy, *Program logics*, fourth lecture: "Shared-memory concurrency: concurrent separation logic", Collège de France, 2021, slides 48–54 (definition of the step-indexed safety predicate, its heap decomposition, and race freedom).
- V. Vafeiadis, "Concurrent separation logic and operational semantics", *MFPS 2011*, ENTCS 276, 2011.
- S. Brookes, "A semantics for concurrent separation logic", *Theoretical Computer Science* 375(1–3):227–270, 2007.
