# Model checking the global logic on choreographies with recursion is undecidable

Whether a choreography of the global calculus with recursion, in a given state, satisfies a formula of the global logic is undecidable.

**Theorem.** The satisfaction problem of the [global logic](global-logic-for-choreographies.md) over the [global calculus](global-calculus.md) with recursion (given a state $\sigma$, a choreography $C$ that may use recursion, and a formula $\phi$, does $C \models_\sigma \phi$ hold?) is undecidable (Theorem 4.3 of the source). Expressions include binary-string values, concatenation with constant strings and equality. An instance is finite: a state assigns binary strings to finitely many located variables, and $C$ and $\phi$ are finite terms.

The source reduces from the Post correspondence problem: a recursive choreography appends randomly chosen pairs of words to $str_1$ and $str_2$, and a formula of the form

$$
\Diamond\big( (str_1@A = str_2@A) \land (str_1@A \ne \epsilon) \land (str_2@A \ne \epsilon) \big)
$$

is meant to hold iff the instance has a solution. Its encoding has a gap at intermediate states (see the expansion), so no cited source proves undecidability for this fixed formula shape; the expansion describes a corrected encoding that would give it.

## Depends on

- [The global calculus of choreographies](global-calculus.md)
- [The global logic for choreographies](global-logic-for-choreographies.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable over the binary alphabet](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/not-tm2-decidable-pcp-bool.md)
- [An injective word homomorphism preserves and reflects PCP solvability](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/pcp-map-iff.md)

## Expansion

The reduction is from the Post correspondence problem over the binary alphabet $\{0, 1\}$; the re-encoding below is an injective word homomorphism, which preserves and reflects solvability. For an instance $(s_1, t_1), \dots, (s_n, t_n)$, participants $A_1, \dots, A_n$ repeatedly open sessions with a participant $B$ and write their index $i$ into the variable $r@B$, so that $r@B$ holds a nondeterministically chosen index. In parallel, participant $A$ repeatedly opens a session with $B$, sends its two current words into $tmp_1@B$ and $tmp_2@B$, and receives them back extended by $s_r$ and $t_r$ according to a conditional on $r@B$ (Definition 4.2 of the source). Both components are recursive, and the initial state has all words empty.

The source's proof sketch argues only that a reachable state with equal non-empty words gives a solution, and as written this fails. In Definition 4.2 the two words are written back in two separate communications, $B \to A : k\langle tmp_1 \cdot s_i, str_1\rangle$ and then $B \to A : k\langle tmp_2 \cdot t_i, str_2\rangle$, so the state between them is reachable and has $str_1 = s_{i_0} \cdots s_{i_{k+1}}$ but $str_2 = t_{i_0} \cdots t_{i_k}$. For the one-pair instance $(s_1, t_1) = (0, 00)$, which has no solution (the two sides have lengths $k+1$ and $2(k+1)$), the first write of the second round gives $str_1 = 00 = str_2$, so the formula holds.

A good expansion states a corrected reduction and links it. One correction keeps the formula: first re-encode the letters by $0 \mapsto 00$ and $1 \mapsto 01$, so that every non-empty genuine word starts with $0$; then in each round write $1 \cdot tmp_1 \cdot s_r$ to $str_1$, then $tmp_2 \cdot t_r$ to $str_2$, then $tmp_1 \cdot s_r$ to $str_1$, all three in the branch that a single conditional on $r@B$ selects, so that they use the same index $r$. In every intermediate state $str_1$ starts with $1$ while $str_2$ is empty or starts with $0$, so the words differ, and at the end of each round $str_1 = s_{i_0} \cdots s_{i_k}$ and $str_2 = t_{i_0} \cdots t_{i_k}$ (re-encoded). Hence the formula holds iff the instance has a solution in which the two words are non-empty. Solutions may consist of empty words: for $\{(\varepsilon, \varepsilon), (0, 00)\}$ the sequence $(1)$ is a solution, but every reachable state with equal words has both words empty. So the reduction first maps every instance containing the pair $(\varepsilon, \varepsilon)$ to a fixed solvable instance such as $\{(0, 0)\}$; in every other instance each pair has a non-empty side, so every solution (a non-empty index sequence with equal concatenations) has non-empty words, and the argument above applies.

The source remarks that the shared store, which lets several threads access the same variables, is what makes the logic this expressive, and conjectures that without variables the logic would be decidable. For recursion-free choreographies it gives a proof system that is sound, complete and terminating (Theorems 5.5, 5.7 and 5.8), so satisfaction is decidable there.

## Sources

- Marco Carbone, Davide Grohmann, Thomas T. Hildebrandt and Hugo A. López, "A Logic for Choreographies", in *Proceedings of the 3rd Workshop on Programming Language Approaches to Concurrency and Communication-cEntric Software (PLACES 2010)*, Electronic Proceedings in Theoretical Computer Science 69, 2011, pp. 29–43, <https://doi.org/10.4204/EPTCS.69.3>; read in arXiv:1110.4159v1, <https://arxiv.org/abs/1110.4159v1>: Definitions 4.1 and 4.2 (the Post correspondence problem and its encoding), Theorem 4.3 with its proof sketch, and the remark after it, in Section 4 ("Undecidability of Global Logic"), and Theorems 5.5, 5.7 and 5.8 in Section 5, in the numbering of that version.
