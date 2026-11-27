# Depth-3 multilinear proofs simulate R$^0$(lin)

Over fields of characteristic $0$, formula multilinear calculus proofs whose lines are depth-3 multilinear formulas polynomially simulate R$^0$(lin); hence they have polynomial-size refutations of the $m$ to $n$ pigeonhole principle and of Tseitin mod $p$ formulas on constant-degree regular graphs.

**Formula multilinear calculus.** Fix a field $\mathbb F$ and multilinear polynomials $Q=\{Q_1,\dots,Q_m\}$ in $\mathbb F[x_1,\dots,x_n,\bar x_1,\dots,\bar x_n]$, where the $\bar x_i$ are formal variables. The *Boolean axioms* are $x_i+\bar x_i-1$ and $x_i\bar x_i$. An *fMC proof* of $g$ from $Q$ is a sequence of multilinear polynomials ending in $g$, each an element of $Q$, a Boolean axiom, or obtained by *product* (from $p$ derive $q\cdot p$ for a polynomial $q$ such that $p\cdot q$ is multilinear) or *addition* (from $p,q$ derive $\alpha p+\beta q$, $\alpha,\beta\in\mathbb F$). Each line is represented as a multilinear arithmetic formula and read as the equation $p=0$; a refutation derives $1$; the size is the total size of the formulas. *Depth-$k$ fMC* requires every line to be a multilinear formula of depth at most $k$.

**Theorem.** Depth-3 fMC proofs over fields of characteristic $0$ polynomially simulate [R$^0$(lin)](r0-lin-fragment.md) proofs. Consequently, over fields of characteristic $0$: for every $m>n$ there are polynomial-size (in $n$) depth-3 fMC refutations of $\mathrm{PHP}^m_n$; and for an $r$-regular graph $G$ with $n$ vertices, $r$ a constant, and a fixed modulus $p$, there are polynomial-size (in $n$) depth-3 fMC refutations of the Tseitin mod $p$ formulas.

## Expansion

An R(lin) line $D=\bigvee_j(\vec a^{(j)}\cdot\vec x=a^{(j)}_0)$ is translated into the product $\widehat D=\prod_j(\vec a^{(j)}\cdot\vec x-a^{(j)}_0)$, which vanishes exactly when $D$ holds; PCR (polynomial calculus with resolution) derives the translated lines with polynomially many steps. For an R$^0$(lin)-line, the multilinearization of $\widehat D$ is a product of a constant number of symmetric polynomials in the blocks, so it has a polynomial-size depth-3 multilinear formula with a plus gate at the root, by a result of Raz and Tzameret on symmetric polynomials over characteristic $0$. An earlier theorem converting PCR refutations whose lines have small multilinear formulas into fMC refutations of the same depth completes the simulation, and the refutations of [pigeonhole and Tseitin mod $p$ in R$^0$(lin)](r0-lin-refutes-php-and-tseitin.md) transfer. The pigeonhole bound improves an earlier result that gave small multilinear proofs only for the functional pigeonhole principle, and the Tseitin refutations work over every field of characteristic $0$, whereas the earlier multilinear refutations needed a field containing a primitive $p$-th root of unity.

## Depends on

- [The fragment R0(lin)](r0-lin-fragment.md)

## Proof depends on

- [R0(lin) refutes pigeonhole and Tseitin mod p formulas](r0-lin-refutes-php-and-tseitin.md)

## Sources

- Ran Raz and Iddo Tzameret, "Resolution over linear equations and multilinear proofs", *Annals of Pure and Applied Logic* 155, 2008, https://doi.org/10.1016/j.apal.2008.04.001; numbering as in arXiv:0708.1529v1 (Section 9.1, Definitions 9.1-9.7; Section 9.2, Definition 9.8, Proposition 3, Corollary 32; Section 9.3, Theorem 33, Proposition 4, Lemma 34, Corollary 35; Section 9.4, Theorems 36 and 37).
