# Coefficient synthesis for threshold automata is undecidable

Threshold automata model fault-tolerant distributed algorithms whose transitions are guarded by comparisons of message counters with linear expressions in parameters such as the number of processes and faults. Choosing the integer coefficients of these guards so that a bad location can never be covered is undecidable, even for acyclic automata.

**Setting (Balasubramanian).** An *environment* $(\Pi, RC, N)$ has finitely many environment variables $\Pi$ over $\mathbb{N}$ (for example the numbers of processes and of faulty processes), a *resilience condition* $RC \subseteq \mathbb{N}^\Pi$ given by a linear formula, and a linear *number function* $N : RC \to \mathbb{N}$ giving the number of modeled processes. A *threshold automaton* has finitely many locations with nonempty initial ones, finitely many shared variables over $\mathbb{N}$, and rules $(\ell, \ell', \varphi, u)$ that move one process from $\ell$ to $\ell'$ when the conjunction $\varphi$ of *threshold guards* $b \cdot x \bowtie a_0 + a_1 p_1 + \dots + a_{|\Pi|} p_{|\Pi|}$ holds ($x$ a shared variable, $p_i \in \Pi$, $b \in \mathbb{N}_{>0}$, $a_i \in \mathbb{Z}$, $\bowtie \in \{<, \le, =, \ge, >\}$), and add $u \in \{0,1\}^{\text{shared}}$ to the shared variables. A configuration fixes parameters in $RC$, a shared-variable valuation and the number of processes in each location, summing to $N$ of the parameters; initial configurations have all processes in initial locations and all shared variables $0$. The automaton *can cover* a location if some run from an initial configuration puts a process there. A *sketch* threshold automaton allows some of the coefficients $b, a_0, \dots, a_{|\Pi|}$ to be integer indeterminates. The *coefficient synthesis problem* (against coverability) asks, given an environment, a sketch and a location $\ell$, whether some integer assignment to the indeterminates yields a threshold automaton that cannot cover $\ell$.

**Theorem (Balasubramanian).** The coefficient synthesis problem against coverability properties is undecidable, even for acyclic threshold automata. The same holds for the non-negative coefficient synthesis problem, in which the indeterminates take non-negative values.

The same paper revisits bounded coefficient synthesis, where the indeterminates range over a given interval and which is decidable, with new upper and lower bounds.

## Depends on

- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof first shows the non-negative version undecidable by reduction from the validity of sentences $\forall \vec{x}\, \exists \vec{y}\, \bigvee_i (\bigwedge (x_j \mid y_k) \wedge \bigwedge A_l(\vec{x}, \vec{y}))$ of Presburger arithmetic with divisibility, with atomic Presburger formulas $A_l$; this fragment is undecidable by earlier work on synthesis for one-counter automata. The indeterminates play the universally quantified variables $\vec{x}$, the parameters and runs of an acyclic sketch guess the $\vec{y}$ and check the matrix, so that the sentence is false exactly when some assignment makes the target location uncoverable. A second reduction transfers the result from non-negative to arbitrary integer coefficients.

## Sources

- A. R. Balasubramanian, "Coefficient Synthesis for Threshold Automata", Automated Technology for Verification and Analysis (ATVA 2022), Lecture Notes in Computer Science, pp. 125–139, 2022, <https://doi.org/10.1007/978-3-031-19135-0_9>; the definitions of Section 2 (environments, threshold automata, coverability and coefficient synthesis) and Theorem 3.1 and Theorem 3.12 (non-negative coefficients) of Section 3 ("Undecidability of Coefficient Synthesis"), and Section 4 on bounded coefficient synthesis of the extended version arXiv:2304.08917v3, read at <https://arxiv.org/abs/2304.08917v3>.
