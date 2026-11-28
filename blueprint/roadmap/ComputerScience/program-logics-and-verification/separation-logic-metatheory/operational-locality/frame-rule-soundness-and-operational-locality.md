# Frame rule soundness is equivalent to safety monotonicity and the frame property

For a relational semantics over a separation algebra with fault-avoiding partial-correctness triples, the frame rule is sound exactly when the relation is safety monotone and has the frame property.

Let $(\Sigma, \bullet, u)$ be a [separation algebra](../abstract-separation-logic/separation-algebras.md) and $R \subseteq \Sigma \times (\Sigma \cup \{\mathit{fault}\})$. For predicates $p, q \subseteq \Sigma$, let $\models \{p\}\, R\, \{q\}$ hold if for every $\sigma \in p$, $(\sigma, \mathit{fault}) \notin R$ and $(\sigma, \sigma') \in R$ implies $\sigma' \in q$; divergence does not falsify a triple. Then $R$ satisfies [safety monotonicity and the frame property](safety-monotonicity-and-the-frame-property.md) if and only if, for all predicates $p, q, r \subseteq \Sigma$,

$$\models \{p\}\, R\, \{q\} \implies\ \models \{p \ast r\}\, R\, \{q \ast r\}.$$

## Depends on

- [Safety monotonicity and the frame property](safety-monotonicity-and-the-frame-property.md)
- [Separation algebras](../abstract-separation-logic/separation-algebras.md)

## Proof depends on

- [Safety monotonicity and the frame property](safety-monotonicity-and-the-frame-property.md)

## Expansion

Forward: take $\sigma = \sigma_0 \bullet \sigma_1$ with $\sigma_0 \in p$ and $\sigma_1 \in r$. $R$ is safe at $\sigma_0$, hence at $\sigma$ by safety monotonicity; if $(\sigma, \sigma') \in R$, the frame property gives $\sigma' = \sigma_0' \bullet \sigma_1$ with $(\sigma_0, \sigma_0') \in R$, so $\sigma_0' \in q$ and $\sigma' \in q \ast r$. Backward, using singleton frames: if $R$ is safe at $\sigma$, then $\models \{\{\sigma\}\}\, R\, \{q_\sigma\}$ for $q_\sigma = \{\tau : (\sigma, \tau) \in R\}$, and framing with $\{\sigma_1\}$ gives safety at $\sigma \bullet \sigma_1$ and that every outcome there lies in $q_\sigma \ast \{\sigma_1\}$, which is the frame property. Cancellativity is not used. Concrete one-way counterparts for heap languages with stores, with a side condition on modified variables, are the partial-correctness [frame rule](../../separation-logic/frame.md) and [the total-correctness frame rule for the heap language](total-correctness-frame-rule-for-heap-language.md).

## Sources

- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007, pp. 366–378, <https://doi.org/10.1109/LICS.2007.30>, author copy <https://www.cs.ox.ac.uk/people/hongseok.yang/paper/asl-short.pdf>, Section 3, Conceptual Development: the statement that a relation satisfies Safety Monotonicity and the Frame Property if and only if the frame rule is sound for it; Definition 6 (fault-avoiding semantic triples).
- H. Yang and P. O'Hearn, "A semantic basis for local reasoning", *Foundations of Software Science and Computation Structures (FoSSaCS 2002)*, LNCS 2303, Springer, 2002, pp. 402–416, <https://doi.org/10.1007/3-540-45931-6_28>, author copy <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf>, Section 4 (the two properties and their role in the soundness of the frame rule).
