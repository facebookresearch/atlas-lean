# Relaxed solvability is polynomial and necessary

For a STRIPS task in positive normal form with atom set $F$ and operator set $O$, and a state $s$:

1. the relaxed task is solvable from $s$ if and only if the goal is contained in the relaxed reachable
   set from $s$;
2. the relaxed reachable set is reached after at most $\lvert F \rvert + 1$ rounds of the fixed-point
   iteration, each scanning all operators, so it is computed in time polynomial in $\lvert F \rvert$ and
   $\lvert O \rvert$ (for example $O((\lvert F \rvert + 1) \cdot \lvert O \rvert \cdot \lvert F \rvert)$ with set
   operations of cost $O(\lvert F \rvert)$);
3. every plan of the original task from $s$ is a relaxed plan, so relaxed unsolvability certifies
   unsolvability.

## Depends on

- [Delete relaxation](delete-relaxation.md)

## Sources

- Foundations of AI: Automated Planning: Delete Relaxation Heuristics (slides) — University of Basel AI course (Helmert group): relaxed planning graphs and relaxed reachability. <https://ai.dmi.unibas.ch/_files/teaching/fs26/ai/slides/ai-f04-handout4.pdf>
- T. Bylander, *The computational complexity of propositional STRIPS planning*, Artificial Intelligence 69 (1994) 165–204: PLANSAT is polynomial when operators have only positive preconditions and positive postconditions (Section 2 summary, proved in Section 3). <https://ai.dmi.unibas.ch/_files/teaching/hs20/po/misc/bylander-aij1994.pdf>
