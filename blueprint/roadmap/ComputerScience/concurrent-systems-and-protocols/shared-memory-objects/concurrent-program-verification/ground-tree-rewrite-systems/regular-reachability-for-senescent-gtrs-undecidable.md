# Regular reachability for senescent ground tree rewrite systems is undecidable

Ground tree rewrite systems with state rewrite subtrees of a tree under a finite control; their control-state reachability is undecidable. In senescent systems a tree node may only be rewritten while it is young, measured in control-state changes. This brings control-state reachability back to decidability, but reaching a regular set of trees stays undecidable.

**Setting (Hague).** A *ground tree rewrite system with state* (sGTRS) $G = \langle Q, \Sigma, R \rangle$ has a finite set of control states $Q$, a finite ranked alphabet $\Sigma$ and finitely many rules $(q_1, A_1) \to (q_2, A_2)$, with $q_1, q_2 \in Q$ and $A_1, A_2$ nondeterministic tree automata over $\Sigma$ that do not accept the empty tree. A configuration is a pair $(q, t)$ of a control state and a finite tree over $\Sigma$. There is a transition $(q_1, t_1) \to (q_2, t_2)$ if some rule with control states $q_1, q_2$ has $t_1 = C[t'_1]$ and $t_2 = C[t'_2]$ for a context $C$, a tree $t'_1$ accepted by $A_1$ and a tree $t'_2$ accepted by $A_2$. Along a run, the *age* of a tree node is the number of transitions that changed the control state since the node was last created by a rewrite. A run is *lifespan restricted* with lifespan $k$ if every rewritten node has age at most $k$ when it is rewritten, and a *senescent GTRS* with lifespan $k$ is an sGTRS whose runs are restricted to lifespan-restricted runs. The *regular reachability problem* asks, given a senescent GTRS with lifespan $k$, an initial configuration $(q_{\mathrm{init}}, t_{\mathrm{init}})$, a target control state $q_{\mathrm{dest}}$ and a tree automaton $A$, whether some lifespan-restricted run from $(q_{\mathrm{init}}, t_{\mathrm{init}})$ reaches a configuration $(q_{\mathrm{dest}}, t)$ with $t$ accepted by $A$.

**Theorem (Hague).** The reachability problem for reset Petri nets reduces to the regular reachability problem for senescent GTRS, already with lifespan $1$, so regular reachability for senescent GTRS is undecidable.

In contrast, control-state reachability for senescent GTRS is Ackermann-complete, and senescent GTRS subsume scope-bounded multi-stack pushdown systems.

## Depends on

- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Bottom-up finite tree automata](../../../../../TheoryOfComputation/omega-automata-and-games/logic-and-tree-automata/bottom-up-finite-tree-automata.md)

## Proof depends on

- [Reachability for Petri nets with two reset, transfer or doubling arcs is undecidable](../../../petri-nets/decision-procedures/decision-problems-for-nets-and-vass/extended-nets-and-affine-vass/reachability-with-two-reset-or-transfer-arcs.md)

## Expansion

The senescent GTRS with lifespan $1$ encodes the control state of the reset Petri net in its own control state and the marking of each place $c$ by the number of leaves labeled $c$, created from a spawn leaf. A decrement relabels a $c$-leaf as dead, and every active leaf may rewrite to itself in (almost) every control state, so that it does not fossilize. A reset forces enough control-state changes without refreshing the $c$-leaves, which fossilize; for reachability, the $c$-leaves may also relabel themselves as dead during a reset. On reaching the target control state the system may guess that the target marking is reached and relabel every active $c$-leaf as a target leaf for $c$. The tree automaton accepts the trees with exactly $m(c)$ target leaves for each place $c$ and no leaf still labeled by a place, which rules out leaves that fossilized without being counted. Reachability for reset Petri nets is undecidable (Araki and Kasami).

## Sources

- Matthew Hague, "Senescent ground tree rewrite systems", Proceedings of the Joint Meeting of the Twenty-Third EACSL Annual Conference on Computer Science Logic and the Twenty-Ninth Annual ACM/IEEE Symposium on Logic in Computer Science (CSL-LICS 2014), pp. 1–10, 2014, <https://doi.org/10.1145/2603088.2603112>; the definitions of the sGTRS model and of senescent GTRS with the regular reachability problem, and the theorem reducing reset Petri net reachability to regular reachability in the section "Modelling Power of Senescent GTRSs", of arXiv:1311.4915v1, read at <https://arxiv.org/abs/1311.4915v1>.
