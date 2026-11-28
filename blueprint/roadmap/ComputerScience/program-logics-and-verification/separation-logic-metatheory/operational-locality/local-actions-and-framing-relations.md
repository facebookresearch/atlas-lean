# Local actions correspond to safety-monotone relations with the frame property

Turning a relational semantics into a function into the topped powerset, with fault on top, makes safety monotonicity together with the frame property equivalent to the single locality inequality of local actions. The translation forgets normal outcomes at states that can also fault, which no fault-avoiding triple can observe.

Let $(\Sigma, \bullet, u)$ be a separation algebra and $R \subseteq \Sigma \times (\Sigma \cup \{\mathit{fault}\})$. Define $\mathrm{func}(R) : \Sigma \to P(\Sigma)^\top$ by

$$\mathrm{func}(R)\,\sigma = \begin{cases} \top & \text{if } (\sigma, \mathit{fault}) \in R, \\ \{\sigma' \in \Sigma : (\sigma, \sigma') \in R\} & \text{otherwise.} \end{cases}$$

Then $R$ satisfies [safety monotonicity and the frame property](safety-monotonicity-and-the-frame-property.md) if and only if $\mathrm{func}(R)$ is a [local action](../abstract-separation-logic/local-actions.md), that is,

$$\sigma_1 \# \sigma_2 \implies \mathrm{func}(R)(\sigma_1 \bullet \sigma_2) \sqsubseteq \mathrm{func}(R)\,\sigma_1 \ast \{\sigma_2\}.$$

The empty set is divergence, so the order is the one of partial correctness; for total correctness the source turns $P(\Sigma)^\top$ upside down, identifying divergence with fault.

## Depends on

- [Local actions](../abstract-separation-logic/local-actions.md)
- [Safety monotonicity and the frame property](safety-monotonicity-and-the-frame-property.md)

## Proof depends on

- [Local actions](../abstract-separation-logic/local-actions.md)
- [Safety monotonicity and the frame property](safety-monotonicity-and-the-frame-property.md)

## Expansion

Every $f : \Sigma \to P(\Sigma)^\top$ equals $\mathrm{func}(R_f)$ for $R_f = \{(\sigma, \mathit{fault}) : f\sigma = \top\} \cup \{(\sigma, \sigma') : f\sigma \neq \top,\ \sigma' \in f\sigma\}$, so, as a consequence, local actions are exactly the images of the relations with the two properties. Relations with the same image satisfy the same fault-avoiding triples, since a triple is falsified by a possible fault whatever the other outcomes.

Write $f = \mathrm{func}(R)$. Forward: if $f\sigma_1 = \top$ the inequality is trivial. Otherwise $R$ is safe at $\sigma_1$, hence at $\sigma_1 \bullet \sigma_2$, so $f(\sigma_1 \bullet \sigma_2)$ is the set of outcomes there, and by the frame property each is $\sigma_0' \bullet \sigma_2$ with $\sigma_0' \in f\sigma_1$. Backward: if $R$ is safe at $\sigma$ then $f\sigma \neq \top$, so $f(\sigma \bullet \sigma_1) \sqsubseteq f\sigma \ast \{\sigma_1\} \neq \top$ and $R$ is safe at $\sigma \bullet \sigma_1$; given safety at $\sigma_0$ and $(\sigma_0 \bullet \sigma_1, \sigma') \in R$, the state $\sigma_0 \bullet \sigma_1$ is safe, so $\sigma' \in f(\sigma_0 \bullet \sigma_1) \subseteq f\sigma_0 \ast \{\sigma_1\}$, which is the frame property. The source calls the relational frame property an unpleasant tabulation of an operational fact and adopts the functional formulation for that reason; footprints are developed for it in [footprints of local functions](../footprints-and-small-specifications/footprints-of-local-functions.md).

## Sources

- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007, pp. 366–378, <https://doi.org/10.1109/LICS.2007.30>, author copy <https://www.cs.ox.ac.uk/people/hongseok.yang/paper/asl-short.pdf>, Section 3, Conceptual Development: the locality condition, the claim that $R$ satisfies Safety Monotonicity and the Frame Property if and only if $\mathrm{func}(R)$ is local, footnote 1 (the definition of $\mathrm{func}$) and the aside on total correctness.
- M. Raza and P. Gardner, "Footprints in local reasoning", *Logical Methods in Computer Science* 5(2:4), 2009, <https://doi.org/10.2168/LMCS-5(2:4)2009>, arXiv:0903.1032v2 <https://arxiv.org/abs/0903.1032v2>, Section 2.1, the discussion after Definition 2.6 deriving safety monotonicity and the frame property from locality (numbers from arXiv:0903.1032v2).
