# The MSO+U theory of the natural numbers with order is undecidable

Monadic second-order logic extended by the unbounding quantifier is undecidable on infinite words: no algorithm decides which MSO+U sentences hold in $(\mathbb N, \le)$, in contrast with Büchi's decidability of plain MSO there.

**Theorem (Bojańczyk, Parys and Toruńczyk).** The [MSO+U](monadic-second-order-logic-with-the-unbounding.md) theory of $(\mathbb N, \le)$ is undecidable: there is no algorithm that decides, given a sentence of monadic second-order logic with the unbounding quantifier over the signature $\{\le\}$, whether it holds in $(\mathbb N, \le)$. This is Theorem 1.1 of the source, proved by reducing emptiness of Minsky (counter) machines.

The result uses no set-theoretic hypothesis. It improves an earlier theorem of Bojańczyk, Gogacz, Michalewski and Skrzypczak, who showed, assuming the axiom of constructibility $V = L$, that the MSO+U theory of the complete binary tree is undecidable.

## Depends on

- [Monadic second-order logic with the unbounding quantifier](monadic-second-order-logic-with-the-unbounding.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the emptiness problem for Minsky machines: given a nondeterministic machine with finitely many states and two counters, is there a finite run from a designated initial state with both counters zero to a designated final state? Runs are encoded by sequences of vectors of natural numbers. The key combinatorial fact (Lemmas 2.1 and 2.2) characterizes the dimension of a vector sequence through boundedness properties only: number sequences are *asymptotically equivalent* if they are bounded on the same sets of positions, and a vector sequence of dimension $d$ need not be an asymptotic mix of any vector sequence of dimension $d - 1$. This lets MSO+U, through the unbounding quantifier, define sequences of trees encoded in words in which the degrees of depth-2 nodes tend to infinity and all but finitely many depth-1 nodes have the same degree (Lemma 3.1). For each Minsky machine one computes an MSO+U sentence that holds in $(\mathbb N, \le)$ iff the machine has an accepting run (Lemma 3.2), the counter values being read off from degrees.

## Sources

- M. Bojańczyk, P. Parys and S. Toruńczyk, "The MSO+U Theory of (N, <) Is Undecidable", in *33rd Symposium on Theoretical Aspects of Computer Science (STACS 2016)*, Leibniz International Proceedings in Informatics 47, Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2016, pp. 21:1–21:8, <https://doi.org/10.4230/LIPIcs.STACS.2016.21>; numbers from arXiv:1502.04578v2, <https://arxiv.org/abs/1502.04578v2>: Theorem 1.1, Lemmas 2.1, 2.2, 3.1 and 3.2.
