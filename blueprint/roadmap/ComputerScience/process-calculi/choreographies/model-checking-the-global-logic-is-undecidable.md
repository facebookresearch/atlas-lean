# Model checking the global logic on choreographies with recursion is undecidable

Whether a choreography of the global calculus with recursion, in a given state, satisfies a formula of the global logic is undecidable, already for one fixed shape of eventually-formula.

**Theorem.** The satisfaction problem of the [global logic over the global calculus](global-calculus-and-global-logic.md) with recursion (given a state $\sigma$, a choreography $C$ that may use recursion, and a formula $\phi$, does $C \models_\sigma \phi$ hold?) is undecidable. This holds already for formulas of the form

$$
\Diamond\big( (str_1@A = str_2@A) \land (str_1@A \ne \epsilon) \land (str_2@A \ne \epsilon) \big),
$$

when expressions include binary-string values, concatenation with constant strings and equality.

## Depends on

- [The global calculus and its global logic](global-calculus-and-global-logic.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The reduction is from the Post correspondence problem over $\{0, 1\}$. For an instance $(s_1, t_1), \dots, (s_n, t_n)$, participants $A_1, \dots, A_n$ repeatedly open sessions with a participant $B$ and write their index $i$ into the variable $r@B$, so that $r@B$ holds a nondeterministically chosen index. In parallel, participant $A$ repeatedly opens a session with $B$, sends its two current words, and receives them back extended by $s_{r}$ and $t_{r}$ according to a conditional on $r@B$. Both components are recursive. Starting from the state in which all words are empty, the formula above holds iff some reachable state has equal non-empty words $str_1 = s_{i_0} \cdots s_{i_k}$ and $str_2 = t_{i_0} \cdots t_{i_k}$, that is, iff the instance has a solution. The source's proof is a sketch.

The source remarks that the shared store, which lets several threads access the same variables, is what makes the logic this expressive, and conjectures that without variables the logic would be decidable. For recursion-free choreographies it gives a sound proof system instead.

## Sources

- Marco Carbone, Davide Grohmann, Thomas T. Hildebrandt and Hugo A. López, "A Logic for Choreographies", in *Proceedings of the 3rd Workshop on Programming Language Approaches to Concurrency and Communication-cEntric Software (PLACES 2010)*, Electronic Proceedings in Theoretical Computer Science 69, 2011, pp. 29–43, <https://doi.org/10.4204/EPTCS.69.3>; arXiv:1110.4159v1, <https://arxiv.org/abs/1110.4159v1>: the definition of the PCP encoding, the theorem and its proof sketch, and the following remark, in Section 4 ("Undecidability of Global Logic").
