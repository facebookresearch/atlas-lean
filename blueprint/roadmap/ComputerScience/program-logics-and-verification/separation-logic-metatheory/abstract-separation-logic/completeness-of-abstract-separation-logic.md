# Completeness of abstract separation logic

For every separation algebra and axiom set, $\mathit{Ax} \models \{p\}\, C\, \{q\}$ implies $\mathit{Ax} \vdash \{p\}\, C\, \{q\}$ in [abstract separation logic](abstract-separation-logic-rules.md). The proof uses the *canonical valuation* $v(\mathit{Ax})$, which maps each primitive command $c$ to the meet of the [best local actions](best-local-action.md) $\mathrm{bla}[p, q]$ over the axioms $\{p\}\, c\, \{q\}$ of $\mathit{Ax}$; it is the greatest valuation satisfying $\mathit{Ax}$, so $\mathit{Ax} \models \{p\}\, C\, \{q\}$ holds exactly when $v(\mathit{Ax})$ satisfies $\{p\}\, C\, \{q\}$. Completeness then follows by induction on $C$; the case of a primitive command, which reduces to singleton preconditions with the disjunction rule and then uses the frame rule once per axiom, is the most delicate step.

## Depends on

- [Abstract separation logic](abstract-separation-logic-rules.md)

## Proof depends on

- [The best local action of a specification](best-local-action.md)
- [Local actions form a complete lattice](local-actions-form-a-complete-lattice.md)

## Sources

- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007; extended version of April 13, 2007, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-long.pdf>, Section 5.2, Definition 19, Lemma 20 and Theorem 21.
