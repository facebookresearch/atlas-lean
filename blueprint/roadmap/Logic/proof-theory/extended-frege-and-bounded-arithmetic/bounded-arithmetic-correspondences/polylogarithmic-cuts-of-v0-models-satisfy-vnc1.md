# Polylogarithmic cuts of models of $V^0$ satisfy $VNC^1$

In any model of $V^0$, the initial segment of numbers bounded by a polynomial in the length of some element, with the strings inside it, is a model of the stronger theory $VNC^1$ (Müller). This strengthens a result of Paris and Wilkie, who obtained $VTC^0$.

Let $\mathcal N=(N_1,N_2,\dots)$ be a model of a two-sorted theory. A *cut* $\mathcal M$ of $\mathcal N$ is a substructure with $M_1\subseteq N_1$ closed under $+$ and $\cdot$ and downward closed under $\le$, the same $0$ and $1$, $M_2=\{X\in N_2 : X\subseteq M_1\}$, and all symbols restricted. It is the *polylogarithmic cut* if

$$
x\in M_1 \iff \exists a\in N_1\ \exists k\in\mathbb N\quad x\le |a|^k .
$$

**Theorem (Müller).** Let $\mathcal N\vDash V^0$ and let $\mathcal M$ be the polylogarithmic cut of $\mathcal N$. Then $\mathcal M\vDash VNC^1$.

## Expansion

The key tool is a formalization of Nepomnjaščij's theorem in $V^0$: if $m=|a|$ for some $a\in N_1$, $c,k\in\mathbb N$ and $\varepsilon<1/k$, then every language in $\mathrm{TimeSpace}(m^c,m^{\varepsilon})$ on strings of length $m$ has a $\Sigma^B_0$-definition in $\mathcal N$ on $[0,m^k]$, so the corresponding strings exist in the cut by $\Sigma^B_0$-comprehension (Theorem 3.2). Monotone formula evaluation is computable by a recursive algorithm in polynomial time and logarithmic space, which suffices to produce the evaluation strings required by the axiom MFV inside $\mathcal M$. Müller applies the theorem in two further results. Together with the bounded reflection principle for Frege over $V^0$ it reproves the Filmus–Pitassi–Santhanam theorem that bounded-depth Frege subexponentially simulates Frege (his Theorem 4.1), since $VNC^1$ proves the soundness of Frege. Since $VNC^1$ contains $VTC^0$, the same argument shows that bounded-depth Frege subexponentially simulates $TC^0$-Frege; combined with the polynomially bounded $TC^0$-Frege proofs of $\neg A$ for almost every random 3-CNF $A$ with $n$ variables and $c\cdot n^{1.4}$ clauses (Müller and Tzameret, his Proposition 4.2), it gives subexponential bounded-depth Frege proofs of these formulas (his Theorem 4.3), which have no subexponential resolution refutations.

## Depends on

- [The two-sorted theories $V^0$ and $VNC^1$](two-sorted-theories-v0-and-vnc1.md)

## Proof depends on

None.

## Sources

- Sebastian Müller, "Polylogarithmic cuts in models of V^0", *Logical Methods in Computer Science* 9(1):16, 2013, doi:10.2168/LMCS-9(1:16)2013, arXiv:1303.6075v2 (Section 3: Definition 3.1 of cuts and of the polylogarithmic cut, Theorem 3.1 (Nepomnjaščij), Theorem 3.2, Theorem 3.3; Section 4: Theorem 4.1 (Filmus, Pitassi and Santhanam) and its proof, Proposition 4.2 and Theorem 4.3).
