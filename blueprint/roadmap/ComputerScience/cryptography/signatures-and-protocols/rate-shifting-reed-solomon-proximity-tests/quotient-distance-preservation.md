# Quotienting by answered evaluation claims preserves distance

Let $f:L\to\mathbb{F}$, let $S\subseteq\mathbb{F}$ with $S\cap L=\emptyset$, $|S|< d$, and let $\mathrm{Ans}:S\to\mathbb{F}$ with interpolant $\widehat{\mathrm{Ans}}$ of degree $<|S|$. Define $\mathrm{Quot}(f,S,\mathrm{Ans})(x)=\bigl(f(x)-\widehat{\mathrm{Ans}}(x)\bigr)/V_S(x)$ for $x\in L$, where $V_S(X)=\prod_{s\in S}(X-s)$. If every codeword $u\in\mathrm{RS}[\mathbb{F},L,d]$ with relative distance less than $\delta$ from $f$ satisfies $\hat{u}(s)\ne\mathrm{Ans}(s)$ for some $s\in S$, then $\mathrm{Quot}(f,S,\mathrm{Ans})$ is $\delta$-far from $\mathrm{RS}[\mathbb{F},L,d-|S|]$.

## Proof sketch

Suppose $g=\mathrm{Quot}(f,S,\mathrm{Ans})$ is within distance $\delta$ of a codeword $\hat{q}$ of degree $< d-|S|$. Then $u=\hat{q}V_S+\widehat{\mathrm{Ans}}$ has degree $< d$, agrees with $f$ wherever $g$ agrees with $\hat{q}$ (since $V_S$ is nonzero on $L$), and satisfies $\hat{u}(s)=\mathrm{Ans}(s)$ on $S$, contradicting the hypothesis.

## Depends on

- [Interactive oracle proofs of proximity for Reed–Solomon codes](rs-iopp.md)

## Sources

- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "STIR: Reed–Solomon Proximity Testing with Fewer Queries", CRYPTO (2024), IACR ePrint 2024/390.
