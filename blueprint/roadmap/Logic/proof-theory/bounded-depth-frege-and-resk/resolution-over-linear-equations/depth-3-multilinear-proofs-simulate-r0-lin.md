# Depth-3 multilinear proofs simulate R$^0$(lin)

Over fields of characteristic $0$, formula multilinear calculus proofs whose lines are depth-3 unbounded fan-in multilinear formulas polynomially simulate R$^0$(lin); hence they refute the $m$ to $n$ pigeonhole formulas and the Tseitin mod $p$ formulas of connected constant-degree regular graphs with $n\equiv1\pmod p$ in polynomial size.

**Multilinear formulas.** Fix a field $\mathbb F$. An *arithmetic formula* in this sense is a finite tree with edges directed from the leaves to the root and with unbounded fan-in: every leaf is labelled by an input variable or a field element, every other node is a plus gate or a product gate, any edge may carry a field element by which the polynomial at its tail is multiplied, and there is a unique node of out-degree zero, the root. A plus (product) gate computes the sum (product) of the polynomials on its incoming edges, and the formula computes the polynomial at the root. Its *size* is its number of nodes and its *depth* the maximal number of edges on a path from a leaf to the root. It is a *multilinear formula* if the polynomial computed at *each* gate is multilinear. This is not the fan-in-two model of [arithmetic proof systems](../linear-algebra-in-proof-complexity/arithmetic-proof-systems.md); at fixed depth the two are not interchangeable.

**Formula multilinear calculus.** Fix multilinear polynomials $Q=\{Q_1,\dots,Q_m\}$ in $\mathbb F[x_1,\dots,x_n,\bar x_1,\dots,\bar x_n]$, where the $\bar x_i$ are formal variables. The *Boolean axioms* are $x_i+\bar x_i-1$ and $x_i\bar x_i$. An *fMC proof* of $g$ from $Q$ is a sequence of multilinear polynomials ending in $g$, each an element of $Q$, a Boolean axiom, or obtained by *product* (from $p$ derive $q\cdot p$ for a polynomial $q$ such that $p\cdot q$ is multilinear) or *addition* (from $p,q$ derive $\alpha p+\beta q$, $\alpha,\beta\in\mathbb F$). Each line is represented as a multilinear formula and read as the equation $p=0$; a refutation derives $1$; the size is the total size of the formulas. *Depth-$k$ fMC* requires every line to be a multilinear formula of depth at most $k$. An R(lin) line $D=\bigvee_j(\vec a^{(j)}\cdot\vec x=a^{(j)}_0)$ is given to fMC as the multilinearization of $\prod_j(\vec a^{(j)}\cdot\vec x-a^{(j)}_0)$, which vanishes at a $0/1$ point exactly when $D$ holds.

**Theorem.** Depth-3 fMC proofs over fields of characteristic $0$ polynomially simulate [R$^0$(lin)](r0-lin-fragment.md) proofs. Consequently, over fields of characteristic $0$, with the formulas of [R$^0$(lin) refutes pigeonhole and Tseitin mod $p$ formulas](r0-lin-refutes-php-and-tseitin.md) given to fMC in this translation:

1. for every $m>n$ there are polynomial-size (in $n$) depth-3 fMC refutations of $\neg\mathrm{PHP}^m_n$;
2. for every fixed integer $p\ge2$ and every connected undirected $r$-regular graph $G$ with $n$ vertices, no double edges and $n\equiv1\pmod p$, with $r$ a constant, there are polynomial-size (in $n$) depth-3 fMC refutations of the Tseitin mod $p$ formula $\mathrm{TSE}_{G,p}$.

## Expansion

An R(lin) line $D$ is translated into the product $\widehat D=\prod_j(\vec a^{(j)}\cdot\vec x-a^{(j)}_0)$, and PCR (polynomial calculus with resolution) derives the translated lines with polynomially many steps. For an R$^0$(lin)-line, the multilinearization of $\widehat D$ is a product of a constant number of symmetric polynomials in the blocks, so it has a polynomial-size depth-3 multilinear formula with a plus gate at the root, by a result of Raz and Tzameret on symmetric polynomials over characteristic $0$. An earlier theorem converting PCR refutations whose lines have small multilinear formulas into fMC refutations of the same depth completes the simulation, and the R$^0$(lin) refutations of the pigeonhole and Tseitin formulas transfer. The hypotheses on $G$ and $n$ are needed: for a single edge with $p=2$, giving both directed edges the value $1$ satisfies every constraint. The pigeonhole bound improves an earlier result that gave small multilinear proofs only for the functional pigeonhole principle, and the Tseitin refutations work over every field of characteristic $0$, whereas the earlier multilinear refutations needed a field containing a primitive $p$-th root of unity.

## Depends on

- [The fragment R0(lin)](r0-lin-fragment.md)
- [R0(lin) refutes pigeonhole and Tseitin mod p formulas](r0-lin-refutes-php-and-tseitin.md)

## Proof depends on

None.

## Sources

- Ran Raz and Iddo Tzameret, "Resolution over linear equations and multilinear proofs", *Annals of Pure and Applied Logic* 155, 2008, https://doi.org/10.1016/j.apal.2008.04.001; numbering as in arXiv:0708.1529v1 (Section 6.2, Definition 6.2; Section 9.1, Definitions 9.1-9.7; Section 9.2, Definition 9.8, Proposition 3, Corollary 32; Section 9.3, Theorem 33, Proposition 4, Lemma 34, Corollary 35; Section 9.4, Theorems 36 and 37).
