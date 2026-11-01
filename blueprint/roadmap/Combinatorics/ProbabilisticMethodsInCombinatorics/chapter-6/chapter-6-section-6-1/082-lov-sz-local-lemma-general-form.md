---
article_id: af_d9169c5709bb14bb39a04b4c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: LovaszLocalLemma.lovasz_local_lemma_general
---

# Theorem 6.1.9 (Lovász local lemma; general form)

Let $A_1, \ldots, A_n$ be events. For each $i \in [n]$, let $N(i)$ be such that $A_i$ is independent from $\{A_j : j \notin \{i\} \cup N(i)\}$. If $x_1, \ldots, x_n \in [0, 1)$ satisfy $\mathbb{P}(A_i) \leq x_i \prod_{j \in N(i)} (1 - x_j)$ for all $i \in [n]$, then $\mathbb{P}(\text{none of the events } A_i \text{ occur}) \geq \prod_{i=1}^n (1 - x_i)$.

## Depends on

- [Definition 6.1.2 (Dependency (di)graph)](080-di.md)
- [Definition 6.1.1 (Independence from a set of events)](079-independence-from-a-set-of-events.md)

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 6, Section 6.1](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
