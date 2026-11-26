# Weakest precondition for heap mutation

For every postcondition $Q$, the triple

$$\{(E \mapsto -) \ast ((E \mapsto F) \mathrel{-\!\!\ast} Q)\}\ [E] := F\ \{Q\}$$

is derivable from the [small axiom](small-axioms-of-separation-logic.md) for mutation by the frame rule, with frame $(E \mapsto F) \mathrel{-\!\!\ast} Q$, and the rule of consequence, which uses the [adjunction](adjunction-between-separating-conjunction-and-implication.md) $(E \mapsto F) \ast ((E \mapsto F) \mathrel{-\!\!\ast} Q) \Rightarrow Q$. Its precondition is the weakest precondition of $[E] := F$ for $Q$: mutation behaves as deletion of the cell at $E$ followed by extension with a cell holding $F$.

## Depends on

- [Small axioms of separation logic](small-axioms-of-separation-logic.md)

## Proof depends on

- [Adjunction between separating conjunction and separating implication](adjunction-between-separating-conjunction-and-implication.md)

## Sources

- P. O'Hearn, J. Reynolds and H. Yang, "Local reasoning about programs that alter data structures", *Computer Science Logic (CSL 2001)*, LNCS 2142, Springer, 2001, pp. 1–19, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/localreasoning.pdf>, Section 4 (derived laws, the backward rule for $[E] := F$).
- J. C. Reynolds, "Separation logic: a logic for shared mutable data structures", *Proceedings of the 17th Annual IEEE Symposium on Logic in Computer Science (LICS 2002)*, IEEE, 2002, author copy <https://www.cs.cmu.edu/~jcr/seplogic.pdf>, Section 3 (the example $\{x \mapsto 9 \ast ((x \mapsto 16) \mathrel{-\!\!\ast} p)\}\ [x] := 16\ \{p\}$).
