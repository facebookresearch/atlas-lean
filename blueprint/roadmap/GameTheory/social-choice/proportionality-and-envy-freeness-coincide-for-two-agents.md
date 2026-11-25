# Proportionality and envy-freeness coincide for two agents

For two agents with additive valuations normalized to $V_i(\text{cake}) = 1$, and an allocation $(A_1, A_2)$ of disjoint pieces that is complete for each agent, meaning
$V_i(A_1) + V_i(A_2) = 1$ for $i = 1, 2$, the allocation is proportional if and only if it is envy-free. Completeness is needed: two empty pieces are envy-free but not
proportional. The allocation produced by cut and choose is complete.

## Proof

With completeness, $V_i(A_i) \ge 1/2$ if and only if $V_i(A_i) \ge 1 - V_i(A_i) = V_i(A_{3-i})$. Cut and choose divides the whole cake into two pieces.

## Depends on

- [Cut-and-choose and Dubins-Spanier](cut-and-choose-and-dubins-spanier.md)

## Sources

- A. D. Procaccia, *Cake cutting algorithms*, in *Handbook of Computational Social Choice*, Cambridge University Press, 2016, Chapter 13, Section 13.3 (proportionality and envy-freeness; with two agents an envy-free allocation is proportional, and cut and choose). Background reference.
