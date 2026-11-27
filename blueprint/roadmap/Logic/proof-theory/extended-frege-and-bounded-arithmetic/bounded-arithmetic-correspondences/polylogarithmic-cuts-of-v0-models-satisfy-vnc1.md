# Polylogarithmic cuts of models of $V^0$ satisfy $VNC^1$

In any model of $V^0$, the initial segment of numbers bounded by a polynomial in the length of some element, with the strings inside it, is a model of the stronger theory $VNC^1$ (Müller). This strengthens a result of Paris and Wilkie, who obtained $VTC^0$.

Let $\mathcal N=(N_1,N_2,\dots)$ be a model of a two-sorted theory. A *cut* $\mathcal M$ of $\mathcal N$ is a substructure with $M_1\subseteq N_1$ closed under $+$ and $\cdot$ and downward closed under $\le$, the same $0$ and $1$, $M_2=\{X\in N_2 : X\subseteq M_1\}$, and all symbols restricted. It is the *polylogarithmic cut* if

$$
x\in M_1 \iff \exists a\in N_1\ \exists k\in\mathbb N\quad x\le |a|^k .
$$

**Theorem (Müller).** Let $\mathcal N\vDash V^0$ and let $\mathcal M$ be the polylogarithmic cut of $\mathcal N$. Then $\mathcal M\vDash VNC^1$.

**Consequence.** For almost every random 3-CNF $A$ with $n$ variables and $m=c\cdot n^{1.4}$ clauses, for a large constant $c$, $\neg A$ has subexponential-size bounded-depth Frege proofs, while such formulas have no subexponential resolution refutations; this gives an average-case separation of resolution from bounded-depth Frege.

## Expansion

The key tool is a formalization of Nepomnjaščij's theorem in $V^0$: if $m=|a|$ for some $a\in N_1$, $c,k\in\mathbb N$ and $\varepsilon<1/k$, then every language in $\mathrm{TimeSpace}(m^c,m^{\varepsilon})$ on strings of length $m$ has a $\Sigma^B_0$-definition in $\mathcal N$ on $[0,m^k]$, so the corresponding strings exist in the cut by $\Sigma^B_0$-comprehension (Theorem 3.2). Monotone formula evaluation is computable by a recursive algorithm in polynomial time and logarithmic space, which suffices to produce the evaluation strings required by the axiom MFV inside $\mathcal M$. The consequence combines this with the polynomially bounded $TC^0$-Frege refutations of random 3-CNFs of Müller and Tzameret, since $VNC^1$ contains $VTC^0$.

## Depends on

- [$V^0$ and $VNC^1$ correspond to bounded-depth Frege and Frege](v0-and-vnc1-correspond-to-bounded-depth-frege-and-frege.md)

## Proof depends on

None.

## Sources

- Sebastian Müller, "Polylogarithmic cuts in models of V^0", *Logical Methods in Computer Science* 9(1):16, 2013, doi:10.2168/LMCS-9(1:16)2013, arXiv:1303.6075v2 (Section 3: Definition 3.1 of cuts and of the polylogarithmic cut, Theorem 3.1 (Nepomnjaščij), Theorem 3.2, Theorem 3.3; Section 4: Proposition 4.2 and Theorem 4.3).
