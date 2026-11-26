# Strongest and weakest intuitionistic approximations

An assertion $p$ is *intuitionistic* if, for all stores $s$ and heaps $h \subseteq h'$, $p$ true in $(s, h)$ implies $p$ true in $(s, h')$. For every assertion $p$, $p \ast \mathit{true}$ is the strongest intuitionistic assertion weaker than $p$, and $\mathit{true} \mathrel{-\!\!\ast} p$ is the weakest intuitionistic assertion stronger than $p$. In particular, for intuitionistic $p$ both $(p \ast \mathit{true}) \Rightarrow p$ and $p \Rightarrow (\mathit{true} \mathrel{-\!\!\ast} p)$ are valid. Pure assertions, those independent of the heap, are intuitionistic, and intuitionistic assertions are closed under $\wedge$, $\vee$, $\forall$, $\exists$, $\ast$ and $\mathrel{-\!\!\ast}$.

## Depends on

- [Separating implication](separating-implication.md)

## Sources

- J. C. Reynolds, "Separation logic: a logic for shared mutable data structures", *Proceedings of the 17th Annual IEEE Symposium on Logic in Computer Science (LICS 2002)*, IEEE, 2002, author copy <https://www.cs.cmu.edu/~jcr/seplogic.pdf>, Section 3 (intuitionistic assertions).
