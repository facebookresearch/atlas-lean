# AC$^0[p]$-Frege lower bounds from search-tree hardness

Krajíček reduces size lower bounds for depth-$d$ AC$^0[p]$-Frege refutations of a constant-degree polynomial system to showing that shallow search trees branching on values of low-degree polynomials over $\mathbb F_p$ rarely expose a violated algebraic rule for random maps from a chosen family.

Let $p$ be a prime and let $\mathcal F_n$ be sets of polynomials over $\mathbb F_p$ in variables $\mathrm{Var}(\mathcal F_n)$ such that (1) the polynomials have degree $O(1)$, (2) $|\mathcal F_n|$ and $|\mathrm{Var}(\mathcal F_n)|$ are $n^{O(1)}$, and (3) the system $f=0$, $f\in\mathcal F_n$, contains $x^2-x=0$ for every variable $x$ and is unsolvable in $\mathbb F_p$. Each equation $f=0$ is viewed as the depth-2 formula $MOD_{p,0}(\psi_1,\dots,\psi_k)$ listing each monomial of $f$ as many times as its coefficient, so refutations in $LK_d(MOD_p)$ make sense.

Work in the Boolean quotient: polynomials are multilinear, and for a set $a$ of variables $x_a=\prod_{x\in a}x$ is the squarefree monomial on $a$, so the multilinear product of $x_a$ and $x_b$ is $x_{a\cup b}$. Let $S^{\mathcal F}_{n,e}$ be the $\mathbb F_p$-space of multilinear polynomials in $\mathrm{Var}(\mathcal F_n)$ of degree at most $e$. An *$S^{\mathcal F}_{n,e}$-search tree* is a $p$-ary tree whose inner nodes are labelled by polynomials $g\in S^{\mathcal F}_{n,e}$, whose $p$ outgoing edges are labelled $g=0,\dots,g=p-1$, and whose leaves are labelled by elements of a set $X$; a map $B:S^{\mathcal F}_{n,e}\to\mathbb F_p$ follows the edges $g=B(g)$ to a leaf $T(B)$. Let $\mathrm{Error}^{\mathcal F}_{n,e}$ be the set of tuples $(B1,c)$ for $c\in\mathbb F_p$, $(B1,x)$ for variables $x$, $(B2,f,g)$ for $f,g\in S^{\mathcal F}_{n,e}$, $(B3,x_a,x_b)$ for monomials with $|a\cup b|\le e$, and $(B4,f)$ for $f\in\mathcal F_n$ of degree at most $e$, so that every polynomial named lies in $S^{\mathcal F}_{n,e}$. Such a tuple is an *error for $B$* if $B$ violates the named rule there: $B(c)\ne c$; $B(x)\notin\{0,1\}$; $B(f)+B(g)\ne B(f+g)$; $B(x_a)B(x_b)\ne B(x_{a\cup b})$; or $B(f)\ne0$.

**Theorem.** Let $r=r(n)\ge(\log n)^{\omega(1)}$ and let $\mathcal F_n$ satisfy (1)-(3). For every $d\ge2$ there are $\epsilon_d>0$ and $n_d\ge1$ such that for every nonempty set $\Omega$ of maps $S^{\mathcal F}_{n,r}\to\mathbb F_p$, every $n\ge n_d$ and every $0<\epsilon\le\epsilon_d$ the following holds: if every $S^{\mathcal F}_{n,r}$-search tree $T$ of depth $r$ with leaves labelled by $\mathrm{Error}^{\mathcal F}_{n,r}$ satisfies

$$
\Pr_{B\in\Omega}\bigl[T(B)\text{ is not an error for }B\bigr]>1-2^{-r^{\epsilon}},
$$

then $LK_d(MOD_p)$ has no refutation of the formulas $f=0$, $f\in\mathcal F_n$, of size less than $2^{\Omega(r^{\epsilon})}$.

## Expansion

A size-$s$ refutation is first balanced into a tree of depth $O(\log s)$, which gives Prover a winning strategy in a $t$-round Prover-Liar game with $t=O(\log s)$ (Lemma 2.1): Prover asks truth values of formulas of depth $d+O(1)$ and size at most $2^t$, and Liar must answer consistently, respect $\neg$ and $\bigvee$, and accept every $\mathbf{MOD}_p$-axiom and every hypothesis. Prover's strategy is then converted into a strategy for Alice in an algebraic game against Bob, who assigns $\mathbb F_p$ values to low-degree polynomials subject to the additivity, multiplicativity and axiom rules (B0)-(B4); a strategy of Alice is a search tree. If simple Bobs drawn from $\Omega$ survive every shallow tree with high probability, they can be turned into a winning Liar, contradicting a short refutation. Here $\epsilon_d=1/(2(d+c)+5)$ for an absolute constant $c$. The worked example is the [pigeonhole system](../../../propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md) written as the polynomial equations of Beame et al., and the motivating circuit result is [Smolensky's theorem](../../../../TheoryOfComputation/circuit-complexity/constant-depth-circuit-lower-bounds/smolensky-s-theorem-mod-q-is-not-in-ac0-p.md).

## Depends on

- [AC0[p]-Frege systems](../bounded-depth-frege-systems/ac0p-frege-systems.md)

## Proof depends on

None.

## Sources

- Jan Krajíček, "A reduction of proof complexity to computational complexity for AC0[p] Frege systems", *Proceedings of the American Mathematical Society* 143, 2015, https://doi.org/10.1090/S0002-9939-2015-12610-X; numbering as in arXiv:1311.2501v4 (Section 3, the game rules (B0)-(B4) on the Boolean quotient $S_{n,e}$; Sections 2-5, Lemma 2.1 and Lemma 5.1; Section 6, Theorem 6.1 and its hypothesis (6)).
