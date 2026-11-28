# Ring-closure acceptance in a SELFIES derivation

A ring symbol does not add its bond when it is read: the candidate closure is queued and resolved after the string has been derived. A candidate whose ring atoms coincide, or whose budgets are exhausted, is dropped; the others are added at the largest order both budgets allow.

Let a derivation of a $\nu$-admissible partial graph produce, in order, ring-closure candidates $(u_1, v_1, \beta_1), \dots, (u_r, v_r, \beta_r)$, where $u_j$ is the left ring atom, $v_j$ the right (ring-initiating) atom and $\beta_j$ the bond part of an ordinary, non-stereochemical ring symbol. Candidates are resolved in creation order. Writing $m_1$ and $m_2$ for the bonds that $u_j$ and $v_j$ may still make in the graph as resolved so far:

- if $m_1 = 0$, or $m_2 = 0$, or $u_j = v_j$, the candidate is rejected;
- otherwise, if $u_j$ and $v_j$ are not yet joined, a bond of order

    $$
    d_0 = \min\big(d(\beta_j), m_1, m_2\big)
    $$

    is added;

- otherwise the existing bond, of order $d_1$, is promoted to $\min(3, d_1 + d_0)$.

The rule preserves $\nu$-admissibility. A new bond raises each endpoint's degree by $d_0 \le \min(m_1, m_2)$; a promotion raises both endpoints by $\min(3, d_1 + d_0) - d_1$, which is at most $d_0$ and so again within budget. The cap keeps orders in $\{1,2,3\}$, and the increment can be zero, as it is when $d_1 = 3$.

Two hypotheses are needed and are part of the contract: the graph entering the resolution is $\nu$-admissible and carries at most one order per pair of atoms, and the budgets $m_1, m_2$ are recomputed after each resolved candidate. Deferral matters, since a closure that is admissible when its symbol is read can become inadmissible once later atoms of the chain spend the left ring atom's budget. The source specifies stereochemical ring symbols separately; they differ only in the bond characters written beside the ring tags.

## Depends on

- [Molecular graphs under valence constraints](molecular-graphs-under-valence-constraints.md)
- [The SELFIES chain-derivation grammar](selfies-derivation-grammar.md)
- [Branch and ring index encoding](branch-and-ring-index-encoding.md)

## Proof depends on

None.

## Expansion

A formal development models resolution as a fold over the candidate list with the partially built graph as state and proves the invariant $b(x) \le \nu(\mathrm{type}(x))$ for every vertex. A rejected candidate leaves the state unchanged. For a new bond the increment is $d_0 \le \min(m_1, m_2)$. For a promotion the increment is $\min(3, d_1 + d_0) - d_1 \le d_0 \le \min(m_1, m_2)$, which is the step the naive reading of the rule gets wrong, since the increment is not $d_0$ itself.

## Context

Graduate detail of the SELFIES specification: the step of the decoder that goes beyond context-free replacement, and the one the robustness statement of this chapter needs separately.

## Sources

- Alston Lo, Robert Pollice, AkshatKumar Nigam, Andrew D. White, Mario Krenn and Alán Aspuru-Guzik, *Recent advances in the Self-Referencing Embedded Strings (SELFIES) library*, Digital Discovery 2 (2023) 897–908, Section III E. DOI [10.1039/d3dd00044c](https://doi.org/10.1039/d3dd00044c), PMC10408573.
