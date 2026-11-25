# Strongly continuous contraction semigroups, generators and cores

Let $L$ be a real Banach space. A strongly continuous contraction semigroup on $L$ is a family $(T(t))_{t\ge0}$ of bounded linear operators on $L$ such that $T(0)=I$, $T(s+t)=T(s)T(t)$ for all $s,t\ge0$, $\lVert T(t)\rVert\le1$ for every $t\ge0$, and $t\mapsto T(t)f$ is continuous from $[0,\infty)$ to $L$ for every $f\in L$. Its generator is the linear operator $A$ defined by

$$Af=\lim_{t\to0^+}\frac{T(t)f-f}{t}$$

on the domain $\mathcal D(A)$ of those $f\in L$ for which the limit exists in norm. For a closed linear operator $A$, a core is a subspace $D\subseteq\mathcal D(A)$ such that the closure of the restriction $A|_D$, the operator whose graph is the closure in $L\times L$ of $\{(f,Af):f\in D\}$, is $A$. A Feller semigroup on $C(E)$, for a compact metric space $E$, is a strongly continuous contraction semigroup on $C(E)$ of positive operators with $T(t)1=1$.

## Expansion

A good expansion splits the page into the definition of the semigroup and its generator, the definition of a core, and the Feller specialization, each as a separate definition, and records the matrix exponential $T(t)=e^{tA}$ of a bounded operator $A$ with $\lVert e^{tA}\rVert\le1$ as the basic example, whose generator is $A$ on all of $L$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, <https://doi.org/10.1002/9780470316658>, Chapter 1, Sections 1 and 3.
- A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*, Springer, 1983, Chapter 1.
