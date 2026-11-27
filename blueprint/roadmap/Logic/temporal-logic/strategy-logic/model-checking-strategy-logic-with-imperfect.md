# Model checking strategy logic with imperfect information is undecidable

Model checking strategy logic with imperfect information is undecidable: no algorithm decides whether a given finite concurrent game structure with observations satisfies a given SLi sentence.

**Theorem (Berthon, Maubert, Murano, Rubin and Vardi).** The model-checking problem for [strategy logic with imperfect information](strategy-logic-with-imperfect-information.md) is undecidable: there is no algorithm that, given an SLi sentence $\Phi$ and a finite concurrent game structure with imperfect information $\mathcal{G}$, decides whether $\mathcal{G} \models \Phi$.

The source isolates *hierarchical instances*, in which the observations attached to quantifiers become finer as one goes down the syntax tree of $\Phi$, and proves model checking decidable on them. The model-checking problem for the companion logic QCTL* with imperfect information under the tree semantics is also undecidable (proved in the same source by a reduction from the monadic second-order theory of the binary tree with equal-level predicate).

## Depends on

- [Strategy logic with imperfect information](strategy-logic-with-imperfect-information.md)

## Proof depends on

None.

## Expansion

Deciding whether a coalition of players with imperfect information has a winning strategy in a multi-player game with a reachability objective is undecidable (Peterson, Reif and Azhar). The source states that this problem easily reduces to SLi model checking: such a game is a finite concurrent game structure with one observation per player, and the existence of a winning strategy for the coalition can be expressed by an SLi sentence that quantifies existentially over strategies of the coalition members with their observations, universally over strategies of the opponents with the identity observation, binds the agents and asks for $F\,\mathit{goal}$.

## Sources

- R. Berthon, B. Maubert, A. Murano, S. Rubin and M. Y. Vardi, "Strategy logic with imperfect information", in *32nd Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2017)*, IEEE, 2017, pp. 1–12, doi:10.1109/LICS.2017.8005136; read as the extended version arXiv:1805.12592v2, <https://arxiv.org/abs/1805.12592v2>: the theorem on undecidability of SLi model checking in Section 2.4 of arXiv:1805.12592v2.
