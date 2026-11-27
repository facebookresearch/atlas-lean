# The relative entropy of the target frequencies

Let $p$ be a distribution on $A$ with $p_a > 0$ for every $a$, and let $\lambda$ satisfy $\Phi(\lambda) = \sum_{a,b} p_a p_b e^{\lambda s_{ab}} = 1$. Then, with $q$ the [target frequencies](target-freq.md),

- $\lambda \sum_{a,b} q_{ab} s_{ab} = \sum_{a,b} q_{ab} \log \dfrac{q_{ab}}{p_a p_b}$, and
- $\lambda \sum_{a,b} q_{ab} s_{ab} \ge 0$

(Altschul 1991).

## Sources

- S. F. Altschul, *Amino acid substitution matrices from an information theoretic perspective*, J. Mol. Biol. 219 (1991), 555–565.
