# Angluin's tell-tale characterization of identifiability in the limit

A countable collection $\mathcal{C} = \{L_1, L_2, \dots\}$ of languages is identifiable in the limit from positive examples (by an identifier that is not required to be computable) if and only if every $L_i$ has a finite **tell-tale** $T_i \subseteq L_i$: a finite subset such that no $L_j \in \mathcal{C}$ satisfies $T_i \subseteq L_j \subsetneq L_i$. For indexed families with uniformly decidable membership, identification by a computable identifier holds if and only if the tell-tales can be enumerated uniformly in $i$.

## Proof sketch

Given tell-tales, at step $t$ output the least index $i \le t$ such that $T_i \subseteq S_t \subseteq L_i$ (and an arbitrary index if there is none). Let $z$ be the least index of the target. Eventually $T_z \subseteq S_t$, and always $S_t \subseteq L_z$. Each $L_j$ with $j < z$ either misses some element of $K$, which eventually appears, or strictly contains $K$; in the latter case, if $T_j \not\subseteq K$ the test $T_j \subseteq S_t$ fails forever, while $T_j \subseteq K \subsetneq L_j$ is excluded by the tell-tale property of $L_j$. Hence from some step on the output is $z$. Conversely, if $L_i$ has no tell-tale, then for every finite $T \subseteq L_i$ some $L_j \supseteq T$ is a strict subset of $L_i$; an adversary that alternately feeds elements of $L_i$ and switches to enumerating such an $L_j$ whenever the identifier settles on $i$ (and back once it settles on $j$) produces a single enumeration on which the identifier changes its mind infinitely often.

## Depends on

- [Identification in the limit from positive examples](identification-in-the-limit.md)

## Sources

- D. Angluin, "Inductive Inference of Formal Languages from Positive Data", Information and Control 45 (1980), Theorem 1.
- E. M. Gold, "Language Identification in the Limit", Information and Control 10 (1967).
- J. Li, V. Raman, A. Tewari, "Generation through the Lens of Learning Theory", COLT (2025), arXiv:2410.13714, Theorem 2.3 (the form without computability).
