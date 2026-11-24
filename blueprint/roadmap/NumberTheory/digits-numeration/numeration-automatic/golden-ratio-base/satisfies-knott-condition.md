# Knott's truncation rule

Let $\varphi$ be the golden ratio. Encode a finite base $\varphi$
expansion with digits $0$ and $1$ by the finite set $S \subseteq \mathbb{Z}$ of the positions of
its digits $1$, and write $a_i$ for its digit at position $i$. The expansion satisfies Knott's
condition when it does not end in the digits $0, 1, 1$: if $S$ is nonempty with least element $R$,
then $a_{R+2} a_{R+1} a_R \ne 011$, that is, it is not the case that both $R + 1 \in S$ and
$R + 2 \notin S$. The empty expansion satisfies the condition.

## Sources

- Michel Dekking and Ad van Loon, *Counting Base Phi Representations*, Fibonacci Quarterly 62 (2024), Section 1, Equation (1.1).
