# Lazy butterfly $(X,Y)\mapsto(X+WY,\,X-WY)$ on redundant residues

The decimation-in-time butterfly can also skip modular corrections: with residues kept in $[0,4p)$ and $p<\beta/4$, one conditional subtraction and one precomputed-quotient multiplication return representatives of $X\pm WY$ again in $[0,4p)$.

Let $\beta\ge 2$ be the word base, let $p$ be an integer with $1<p<\beta/4$, let $0<W<p$, and put $W'=\lfloor W\beta/p\rfloor$. Given words $0\le X<4p$ and $0\le Y<4p$, perform the word operations

1. if $X\ge 2p$ then $X\leftarrow X-2p$;
2. $Q\leftarrow\lfloor W'Y/\beta\rfloor$, the high word of the double-word product $W'Y$;
3. $T\leftarrow(WY-Qp)\bmod\beta$, computed from the low words of the products $WY$ and $Qp$;
4. $X'\leftarrow X+T$ and $Y'\leftarrow(X+2p)-T$.

Then $X'\equiv X_0+WY\pmod p$ and $Y'\equiv X_0-WY\pmod p$ for the original input $X_0$, with $0\le T<2p$, $0\le X'<4p$ and $0\le Y'<4p$. Every value stored in a register lies in $[0,\beta)$; the products are double-word products of which only the indicated word is used. In Harvey's setting ($p$ a word-size prime with $p\equiv 1\pmod L$, $W$ a power of a primitive $L$-th root of unity) this butterfly appears when switching to a decimation-in-time transform and in the inverse obtained by running Harvey's Algorithm 1 backwards.

## Depends on

None.

## Proof depends on

- [Modular multiplication by a fixed factor with a precomputed quotient](shoup-precomputed-modular-multiplication.md)

## Expansion

Harvey's proof of Theorem 3: step 1 leaves $X\in[0,2p)$ in the same class modulo $p$. Since $0\le Y<4p<\beta$, the precomputed-quotient bound gives $0\le WY-Qp<Yp/\beta+p<2p$, so $T$ is a representative of $WY$ in $[0,2p)$. Then $X+T\in[0,4p)$ and $(X+2p)-T\in(0,4p)$, both below $\beta$.

## Sources

- David Harvey, "Faster arithmetic for number-theoretic transforms", Journal of Symbolic Computation 60 (2014), 113–119, DOI [10.1016/j.jsc.2013.09.002](https://doi.org/10.1016/j.jsc.2013.09.002); read as arXiv:1205.2926v2: §1 (setting), §4, Algorithm 4 (modified inverse butterfly) and Theorem 3.
