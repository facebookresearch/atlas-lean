# Modular multiplication by a fixed factor with a precomputed quotient

Shoup's method multiplies by a fixed residue $W$ modulo a word-size modulus $p<\beta/2$ using the precomputed word $W'=\lfloor W\beta/p\rfloor$: one high-word product estimates the quotient, the remainder candidate lies in $[0,2p)$, and one conditional subtraction finishes.

Let $\beta\ge 2$ be the word base (for example $\beta=2^{64}$), let $p$ be an integer with $1<p<\beta/2$, and let $W$ be an integer with $0<W<p$. Put $W'=\lfloor W\beta/p\rfloor$, so $0<W'<\beta$. For every integer $T$ with $0\le T<\beta$, let $Q=\lfloor W'T/\beta\rfloor$ (the high word of the double-word product $W'T$). Then

$$
WT-Qp\equiv WT\pmod p\qquad\text{and}\qquad 0\le WT-Qp<\frac{Tp}{\beta}+p<2p<\beta .
$$

Consequently $WT-Qp=(WT-Qp)\bmod\beta$ is obtained from the low words of the products $WT$ and $Qp$, and $WT\bmod p$ follows by one conditional subtraction of $p$. The input $T$ need not be reduced modulo $p$.

## Depends on

None.

## Proof depends on

None.

## Expansion

Harvey's proof of Theorem 1: by definition $0\le W\beta/p-W'<1$ and $0\le W'T/\beta-Q<1$; multiplying the first by $Tp/\beta$ and the second by $p$ and adding gives $0\le WT-Qp<Tp/\beta+p$, and $Tp/\beta<p$ because $T<\beta$. The first observation of Harvey's §3 notes that the argument only uses $0\le T<\beta$.

## Sources

- David Harvey, "Faster arithmetic for number-theoretic transforms", Journal of Symbolic Computation 60 (2014), 113–119, DOI [10.1016/j.jsc.2013.09.002](https://doi.org/10.1016/j.jsc.2013.09.002); read as arXiv:1205.2926v2: §2, Algorithm 2 (input condition $p<\beta/2$) lines 5–7 and the proof of Theorem 1, and the first observation of §3.
