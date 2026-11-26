# Cook–Reckhow propositional proof systems

For a language $L \subseteq \Sigma^*$, a *proof system* for $L$ is a polynomial-time computable function $f : \Sigma_1^* \to \Sigma^*$, for some alphabet $\Sigma_1$, whose range is exactly $L$; a string $x$ with $f(x) = y$ is a *proof* of $y$. The proof system is *polynomially bounded* if there is a polynomial $p$ such that every $y \in L$ has a proof $x$ with $|x| \le p(|y|)$. A *propositional proof system* is a proof system for the set $\mathrm{TAUT}$ of (encodings of) propositional tautologies. If $f_1$ and $f_2$ are proof systems for $L$, then $f_2$ *p-simulates* $f_1$ if there is a polynomial-time computable function $g$ with $f_2(g(x)) = f_1(x)$ for every $x$. The relation of p-simulation is reflexive and transitive, and a proof system that p-simulates a polynomially bounded proof system for the same language is itself polynomially bounded.

## Depends on

- [Polynomial-time computable functions](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Sources

- S. A. Cook and R. A. Reckhow, "The relative efficiency of propositional proof systems", *Journal of Symbolic Logic* 44(1):36–50, 1979, <https://www.cs.toronto.edu/~sacook/homepage/cook_reckhow.pdf>, Section 1, Definitions 1.3 and 1.5 and Proposition 1.6
