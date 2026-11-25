# Kleene iteration from the bottom stabilizes on a finite partial order

Let $A$ be a partially ordered set with a least element $\bot$ and let $F : A \to A$ be monotone. Write $F^k$ for the $k$-fold iterate of $F$, with $F^0$ the identity, so the Kleene iterates from the bottom are $\bot,\ F(\bot),\ F(F(\bot)),\ \dots$. Assume moreover that $A$ is finite. Then there is $k \in \mathbb{N}$ with

$$F^k(\bot) = F\bigl(F^k(\bot)\bigr),$$

that is, some Kleene iterate from $\bot$ is a fixed point of $F$. No bound on $k$ is asserted and no lattice structure beyond the least element is assumed.

This is the termination argument of Kildall's iterative dataflow analysis: the transfer function is monotone on a finite lattice of abstract states.
