# Soundness of abstract separation logic

Every rule of [abstract separation logic](abstract-separation-logic-rules.md) preserves semantic validity $\mathit{Ax} \models \{p\}\, C\, \{q\}$, so $\mathit{Ax} \vdash \{p\}\, C\, \{q\}$ implies $\mathit{Ax} \models \{p\}\, C\, \{q\}$ for every separation algebra and axiom set. Soundness of the frame rule is the locality condition of local actions, and the other rules are straightforward.

## Depends on

- [Abstract separation logic](abstract-separation-logic-rules.md)

## Sources

- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007; extended version of April 13, 2007, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-long.pdf>, Section 5.2, Theorem 18.
