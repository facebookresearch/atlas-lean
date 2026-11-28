# Universal zenoness and semantic boundedness of dense-timed Petri nets are undecidable

In dense-timed Petri nets every token carries a real-valued age. Whether some computation is zeno (infinite but taking finite time) is decidable, but whether every infinite computation is zeno is undecidable, and so is boundedness when only tokens that can still be consumed are counted.

**Setting (Abdulla, Mahata and Mayr).** A timed Petri net (TPN) has finite sets of places and transitions; each input arc and each output arc between a transition and a place carries a time interval with natural-number bounds (possibly $\infty$ as upper bound), open, closed or half-open. A marking is a finite multiset of tokens $(p, x)$, a place with a nonnegative real age. A *timed transition* adds the same positive real $x$ to the ages of all tokens; firing a transition removes one token from each input place whose age lies in the arc's interval and adds to each output place a token whose age is chosen in the output arc's interval. The semantics is lazy: enabled transitions need not fire. The delay $\Delta(\pi)$ of a computation $\pi$ is the sum of its timed steps. A token $(p, x)$ of a marking $M$ is *semantically live* if some finite computation $\pi$ from $M$ reaches a marking in which the aged token $(p, x + \Delta(\pi))$ can be consumed by an enabled transition; $L(M)$ is the set of live tokens of $M$.

- *Universal zenoness:* given a TPN and a marking $M$, is $\Delta(\pi)$ finite for every infinite computation $\pi$ from $M$?
- *Semantic boundedness:* given a TPN and an initial marking $M_0$, is the size of $L(M)$ bounded over all markings $M$ reachable from $M_0$?

**Theorem (Abdulla, Mahata and Mayr).** Universal zenoness and semantic boundedness are undecidable for timed Petri nets.

In contrast, the same paper shows that zenoness (existence of a zeno computation), existence of arbitrarily fast computations, token liveness and syntactic boundedness (counting all tokens) are decidable.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Lossy counter machines](../../../../distributed-execution-models/parameterized-and-infinite-state-verification/lossy-counter-machines/lossy-counter-machines.md)

## Expansion

Both proofs encode lossy counter machines. For universal zenoness the authors reduce from Mayr's undecidable problem whether some initial counter value $n$ gives a lossy counter machine with four counters an infinite computation from $(q_0, n, 0, 0, 0)$. The simulating net first puts an arbitrary number $n$ of tokens on the first counter place by a loop taking zero time, then simulates the machine from $(q_0, n, 0, 0, 0)$, waiting one time unit during every simulated instruction, so it has no zeno runs that simulate the machine; during the wait the counter tokens can be refreshed to age $0$, and tokens that are not refreshed grow too old and count as lost, which matches lossiness. Hence the net has a non-zeno infinite computation exactly when the machine has an infinite computation from $(q_0, n, 0, 0, 0)$ for some $n$. (The paper's lossy counter machines replace zero tests by resets, which it notes is equivalent for lossy machines.) For semantic boundedness, the same kind of encoding makes the live tokens (of age below $1$) correspond to the counter values, so the net is semantically bounded exactly when the lossy counter machine is bounded, which is undecidable by Mayr's result.

## Sources

- Parosh Abdulla, Pritha Mahata and Richard Mayr, "Dense-Timed Petri Nets: Checking Zenoness, Token liveness and Boundedness", Logical Methods in Computer Science 3(1), 2007, <https://doi.org/10.2168/LMCS-3(1:1)2007>; the definitions of the section "Timed Petri Nets and Regions" and of token liveness, the section "Universal Zenoness" (the lossy counter machine problem and the two undecidability theorems) and the semantic boundedness theorem of the section "Boundedness", read in arXiv:cs/0611048v2, <https://arxiv.org/abs/cs/0611048v2>.
