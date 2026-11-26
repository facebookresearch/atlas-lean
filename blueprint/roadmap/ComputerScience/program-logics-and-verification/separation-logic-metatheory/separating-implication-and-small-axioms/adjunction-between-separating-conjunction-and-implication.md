# Adjunction between separating conjunction and separating implication

For all assertions $p_1, p_2, p_3$ of separation logic, $p_1 \ast p_2 \Rightarrow p_3$ is valid if and only if $p_1 \Rightarrow (p_2 \mathrel{-\!\!\ast} p_3)$ is valid, where $\ast$ and $\mathrel{-\!\!\ast}$ are the [separating conjunction and separating implication](separating-implication.md). Equivalently, both directions of the inference between these two implications are sound. Separating conjunction is also monotone: if $p_1 \Rightarrow p_2$ and $q_1 \Rightarrow q_2$ are valid, so is $p_1 \ast q_1 \Rightarrow p_2 \ast q_2$.

## Depends on

- [Separating implication](separating-implication.md)

## Sources

- J. C. Reynolds, "Separation logic: a logic for shared mutable data structures", *Proceedings of the 17th Annual IEEE Symposium on Logic in Computer Science (LICS 2002)*, IEEE, 2002, author copy <https://www.cs.cmu.edu/~jcr/seplogic.pdf>, Section 3 (the inference rules for $\ast$ and the two rules expressing the adjunction).
