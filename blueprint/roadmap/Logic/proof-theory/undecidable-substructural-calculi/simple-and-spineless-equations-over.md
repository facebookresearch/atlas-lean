# Simple and spineless equations over commutative residuated lattices

Simple equations over commutative residuated lattices are inequalities $x_1 \cdots x_n \leq \bigvee_{d \in D} x_1^{d(1)} \cdots x_n^{d(n)}$, the algebraic form of structural rules of the substructural logic $\mathsf{FL_e}$; spineless equations are those that no substitution turns into a spinal, triangular, shape.

**Residuated lattices.** A *residuated lattice* $(R, \vee, \wedge, \cdot, \backslash, /, 1)$ is a lattice $(R, \vee, \wedge)$ with a monoid $(R, \cdot, 1)$ such that $xy \leq z \iff x \leq z/y \iff y \leq x\backslash z$. It is *commutative* if the monoid is; then $x \to y := x\backslash y = y/x$. Residuated lattices form a variety $\mathsf{RL}$ and the commutative ones a variety $\mathsf{CRL}$; they are the algebraic semantics of the Full Lambek calculus $\mathsf{FL}$ (without the constant $0$) and of $\mathsf{FL_e}$ (with exchange), and an extension of $\mathsf{FL_e}$ by structural rules corresponds to a subvariety of $\mathsf{CRL}$ axiomatized by equations in $\{\vee, \cdot, 1\}$.

**Simple equations.** For a finite nonempty set $D$ of column vectors in $\mathbb{N}^n$ with no row that is zero in every $d \in D$, the *simple equation* $[D]$ is

$$
x_1 x_2 \cdots x_n \ \leq\ \bigvee_{d \in D} x_1^{d(1)} \cdots x_n^{d(n)} .
$$

Over $\mathsf{CRL}$ every $\{\vee,\cdot,1\}$-equation is equivalent to a finite set of *basic* equations $t_0 \leq t_1 \vee \cdots \vee t_l$ (monoid terms with the same variables on both sides), and each basic equation is equivalent to a simple one, its linearization. A one-variable basic equation is written $[n,P] : x^n \leq \bigvee_{p \in P} x^p$.

**Spinal and spineless.** A basic equation $x_1^{f(1)} \cdots x_k^{f(k)} \leq (1 \vee)\, \bigvee_{i=1}^{k} x_1^{s_i(1)} \cdots x_i^{s_i(i)}$ is *spinal* if its left-hand exponent vector $f$ is not among the right-hand ones, and each nonzero right-hand vector $s_i$ has $s_i(i) \neq 0$ and $s_i(j) = 0$ for $j > i$ (an upper-triangular "spine"; the joinand $1$ may or may not occur). A simple equation is *prespinal* if some substitution of monoid terms for its variables maps it to a spinal equation, and *spineless* otherwise; a simple equation for $\mathsf{RL}$ is spineless if its commutative version is. A simple equation is *expansive* if it has a substitution instance $x^n \leq \bigvee_{j=1}^m x^{n + c_j}$ with $n, m \geq 1$ and all $c_j \geq 1$.

**Decision problems.** A variety $\mathcal{V}$ has *undecidable word problem* if for some finite presentation $\langle X, E \rangle$ no algorithm decides, for terms $s, t$, whether the quasiequation $\& E \Rightarrow s = t$ is valid in $\mathcal{V}$; then its quasiequational theory (deducibility in the logic) is undecidable too. The *equational theory* corresponds to theoremhood in the logic.

## Depends on

None.

## Proof depends on

None.

## Expansion

The one-variable spinal equations are the knotted inequalities $x^n \leq x^m$ and their variants $x^n \leq 1 \vee x^m$ with $n \neq m$. The linearization of $[n,P]$ is spineless iff $[n,P]$ is trivial ($n \in P$) or $P$ contains two distinct positive integers (Lemma 5.4); for instance $x \leq x^2 \vee x^3$, corresponding to the structural rule deriving $\Gamma, \Delta, \Sigma \vdash \Pi$ from $\Gamma, \Delta, \Delta, \Sigma \vdash \Pi$ and $\Gamma, \Delta, \Delta, \Delta, \Sigma \vdash \Pi$, is spineless and expansive.

## Sources

- Nikolaos Galatos and Gavin St. John, "Most simple extensions of $\mathsf{FL_e}$ are undecidable", *The Journal of Symbolic Logic* 87(3):1156–1200, 2022, doi:10.1017/jsl.2021.46; read as arXiv:2005.00645v1, <https://arxiv.org/abs/2005.00645v1>: Section 1 (residuated lattices and the example rule), Section 2 (presentations and the word problem), Section 5 (basic and simple equations, Definitions 5.2 and 5.3 of spinal and spineless equations, Lemma 5.4 and expansive equations) of arXiv:2005.00645v1.
