# Soundness of abstract separation logic

Every rule of [abstract separation logic](abstract-separation-logic-rules.md) preserves semantic validity $\mathit{Ax} \models \{p\}\, C\, \{q\}$, so $\mathit{Ax} \vdash \{p\}\, C\, \{q\}$ implies $\mathit{Ax} \models \{p\}\, C\, \{q\}$ for every separation algebra and axiom set. Soundness of the frame rule is the locality condition of local actions, and the other rules are straightforward.

## Depends on

- [Abstract separation logic](abstract-separation-logic-rules.md)

## Sources

- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007, pp. 366–378, <https://doi.org/10.1109/LICS.2007.30>, author copy <https://www.cs.ox.ac.uk/people/hongseok.yang/paper/asl-short.pdf>, Section 5, Theorem 16 and the sentence after it.
