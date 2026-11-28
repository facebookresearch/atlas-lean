# Lazy butterfly $(X,Y)\mapsto(X+Y,\,W(X-Y))$ on redundant residues

Harvey's butterfly keeps residues modulo $p$ in the redundant range $[0,2p)$ and skips the final corrections: for $p<\beta/4$ it maps register inputs in $[0,2p)$ to representatives of $X+Y$ and $W(X-Y)$ in $[0,2p)$, ready for the next butterfly.

Let $\beta\ge 2$ be the word base, let $p$ be an integer with $1<p<\beta/4$, let $0<W<p$, and put $W'=\lfloor W\beta/p\rfloor$. Given words $0\le X<2p$ and $0\le Y<2p$, perform the word operations

1. $X'\leftarrow X+Y$; if $X'\ge 2p$ then $X'\leftarrow X'-2p$;
2. $T\leftarrow(X+2p)-Y$;
3. $Q\leftarrow\lfloor W'T/\beta\rfloor$, the high word of the double-word product $W'T$;
4. $Y'\leftarrow(WT-Qp)\bmod\beta$, computed from the low words of the products $WT$ and $Qp$.

Then $X'\equiv X+Y\pmod p$ and $Y'\equiv W(X-Y)\pmod p$, with $0\le X'<2p$ and $0\le Y'<2p$. Every value stored in a register ($X'$, $X+2p$, $T$, $Q$, $Y'$) lies in $[0,\beta)$, so no stored word overflows or underflows; the products $W'T$, $WT$, $Qp$ are double-word products of which only the indicated word is used. In Harvey's number-theoretic transform, $p$ is a word-size prime with $p\equiv 1\pmod L$ for the transform length $L$, and $W$ is a power of a fixed primitive $L$-th root of unity; this is the decimation-in-frequency butterfly, and normalizing final outputs to $[0,p)$ costs one extra pass.

## Depends on

None.

## Proof depends on

- [Modular multiplication by a fixed factor with a precomputed quotient](shoup-precomputed-modular-multiplication.md)

## Expansion

Harvey's proof of Theorem 2: step 1 returns a representative of $X+Y$ in $[0,2p)$ without overflow because $X+Y<4p<\beta$. Step 2 gives $0<T<4p<\beta$ with $T\equiv X-Y\pmod p$. The precomputed-quotient bound $0\le WT-Qp<Tp/\beta+p$ applies to any $0\le T<\beta$, and $Tp/\beta<4p^{2}/\beta<p$, so $WT-Qp\in[0,2p)$ and equals its residue modulo $\beta$.

## Sources

- David Harvey, "Faster arithmetic for number-theoretic transforms", Journal of Symbolic Computation 60 (2014), 113–119, DOI [10.1016/j.jsc.2013.09.002](https://doi.org/10.1016/j.jsc.2013.09.002); read as arXiv:1205.2926v2: §1 (setting: word-size prime $p\equiv 1\pmod L$, Algorithm 1), §3, Algorithm 3 (modified Shoup butterfly) and Theorem 2.
