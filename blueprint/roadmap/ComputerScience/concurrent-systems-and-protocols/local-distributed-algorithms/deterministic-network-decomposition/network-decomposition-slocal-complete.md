# Network decomposition is complete for polylogarithmic sequential locality

Computing a $(\mathrm{poly}\log n, \mathrm{poly}\log n)$-network decomposition is $\mathrm{P}\text{-}\mathrm{SLOCAL}$-complete under polylogarithmic-round deterministic LOCAL reductions: it lies in $\mathrm{P}\text{-}\mathrm{SLOCAL}$, and if it can be solved in $\mathrm{poly}(\log n)$ deterministic LOCAL rounds then $\mathrm{P}\text{-}\mathrm{LOCAL} = \mathrm{P}\text{-}\mathrm{SLOCAL}$. Furthermore $\mathrm{P}\text{-}\mathrm{RLOCAL} \subseteq \mathrm{P}\text{-}\mathrm{SLOCAL}$ for problems whose solutions can be checked deterministically in polylogarithmic rounds.

## Proof sketch

Ball carving is a sequential local procedure with polylogarithmic locality, giving membership. Completeness is the conversion lemma applied with a polylogarithmic decomposition of the appropriate power graph. For the randomized inclusion, run the randomized algorithm in SLOCAL using the method of conditional expectations: each vertex, when processed, fixes its random bits to keep the conditional probability of a locally checkable failure small, which is possible because failure events depend only on polylogarithmic neighbourhoods.

## Depends on

- [The SLOCAL model and its polylogarithmic class](the-slocal-model.md)
- [Network decomposition with weak or strong diameter](network-decomposition-weak-strong-diameter.md)
- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Network decompositions convert sequential local algorithms into LOCAL algorithms](slocal-to-local-via-network-decomposition.md)
- [Ball carving: every graph has an (O(log n), O(log n)) strong-diameter decomposition](ball-carving-network-decomposition-existence.md)

## Sources

- M. Ghaffari, F. Kuhn, Y. Maus, "On the Complexity of Local Distributed Graph Problems", STOC 2017, arXiv:1611.02663.
- M. Ghaffari, D. G. Harris, F. Kuhn, "On Derandomizing Local Distributed Algorithms", FOCS 2018, arXiv:1711.02194.
