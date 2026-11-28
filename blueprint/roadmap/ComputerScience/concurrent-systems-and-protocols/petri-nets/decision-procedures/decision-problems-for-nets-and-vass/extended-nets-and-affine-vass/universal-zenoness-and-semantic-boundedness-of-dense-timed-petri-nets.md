# Universal zenoness and semantic boundedness of dense-timed Petri nets are undecidable

In dense-timed Petri nets every token carries a real-valued age. Whether some computation is zeno (infinite but taking finite time) is decidable, but whether every infinite computation is zeno is undecidable, and so is boundedness when only tokens that can still be consumed are counted.

**Setting (Abdulla, Mahata and Mayr).** A timed Petri net (TPN, Definition 2.2) has finite sets of places and transitions; each input arc and each output arc between a transition and a place carries a time interval with natural-number bounds (possibly $\infty$ as upper bound), open, closed or half-open. A marking is a finite multiset of tokens $(p, x)$, a place with a nonnegative real age; as an input to the problems below, a marking is given by its finitely many tokens with rational ages (the universal-zenoness reduction uses the marking $[(q_{\mathrm{init}}, 0)]$, one token of age $0$). A *timed transition* adds the same positive real $x$ to the ages of all tokens; firing a transition removes one token from each input place whose age lies in the arc's interval and adds to each output place a token whose age is chosen in the output arc's interval. The semantics is lazy: enabled transitions need not fire. As in the source, a *computation* alternates nonempty blocks of discrete transitions with single timed transitions of positive delay: it may start with one timed transition, but no two timed transitions follow each other, so every infinite computation contains infinitely many discrete transitions (Section 2, "Computations"). The delay $\Delta(\pi)$ of a computation $\pi$ is the sum of its timed steps. A token $(p, x)$ of a marking $M$ is *semantically live* if some finite computation $\pi$ from $M$ reaches a marking in which the aged token $(p, x + \Delta(\pi))$ can be consumed by an enabled transition; $L(M)$ is the sub-multiset of $M$ formed by its semantically live tokens (Definition 7.1), a marking whose size $|L(M)|$ counts live tokens with multiplicity (Section 8).

- *Universal zenoness:* given a TPN and a marking $M$, is $\Delta(\pi)$ finite for every infinite computation $\pi$ from $M$?
- *Semantic boundedness:* given a TPN and an initial marking $M_0$, is the number $|L(M)|$ of live tokens, counted with multiplicity, bounded over all markings $M$ reachable from $M_0$? That is, is $\mathrm{maxsize}(\mathit{Reach}^l(M_0))$ bounded, where $\mathit{Reach}^l(M_0) = \{L(M) : M_0 \to^* M\}$ (Section 8)?

**Theorem (Abdulla, Mahata and Mayr).** Universal zenoness and semantic boundedness are undecidable for timed Petri nets (Theorems 6.4 and 8.4).

In contrast, the same paper shows that zenoness (existence of a zeno computation, Theorem 3.42), existence of arbitrarily fast computations (Section 5), token liveness (Theorem 7.3) and syntactic boundedness, counting all tokens (Theorem 8.2), are decidable.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Lossy counter machines](../../../../distributed-execution-models/parameterized-and-infinite-state-verification/lossy-counter-machines/lossy-counter-machines.md)
- [Finiteness of reachability sets of lossy counter machines is Σ⁰₁-complete](../../../../distributed-execution-models/parameterized-and-infinite-state-verification/lossy-counter-machines/finiteness-for-lossy-counter-machines-sigma01-complete.md)

## Expansion

Both proofs encode lossy counter machines. For universal zenoness the authors reduce from Mayr's undecidable problem whether some initial counter value $n$ gives a lossy counter machine with four counters an infinite computation from $(q_0, n, 0, 0, 0)$ (Theorem 6.1 of the source), through its negation, the non-zenoness problem (Lemma 6.2 and Theorem 6.3). The simulating net first puts an arbitrary number $n$ of tokens on the first counter place by a loop taking zero time, then simulates the machine from $(q_0, n, 0, 0, 0)$, waiting one time unit during every simulated instruction, so it has no zeno runs that simulate the machine; during the wait the counter tokens can be refreshed to age $0$, and tokens that are not refreshed grow too old and count as lost, which matches lossiness. Hence the net has a non-zeno infinite computation exactly when the machine has an infinite computation from $(q_0, n, 0, 0, 0)$ for some $n$. (The paper's lossy counter machines replace zero tests by resets, which it notes is equivalent for lossy machines.) For semantic boundedness, the same kind of encoding makes the live tokens (of age below $1$) correspond to the counter values, so the net is semantically bounded exactly when the lossy counter machine is bounded, that is, has a finite reachability set, which is undecidable by Mayr's result. A good expansion adds a page for Mayr's theorem that it is undecidable whether some initial value $n$ gives a four-counter lossy counter machine an infinite computation from $(q_0, n, 0, 0, 0)$.

## Sources

- Parosh Abdulla, Pritha Mahata and Richard Mayr, "Dense-Timed Petri Nets: Checking Zenoness, Token liveness and Boundedness", Logical Methods in Computer Science 3(1), 2007, <https://doi.org/10.2168/LMCS-3(1:1)2007>; Definition 2.2 in Section 2 ("Timed Petri Nets and Regions"), Theorem 3.42, Section 5, Section 6 ("Universal Zenoness": Theorem 6.1, Lemma 6.2, Theorems 6.3 and 6.4), Definition 7.1 and Theorem 7.3 in Section 7, and Theorems 8.2 and 8.4 in Section 8, read in arXiv:cs/0611048v2, <https://arxiv.org/abs/cs/0611048v2>.
