# Lindsey's lemma over GF(2)

Let $B$ be an $\alpha\times\beta$ matrix over $\mathbb{F}_2$, let $P\subseteq\mathbb{F}_2^{\alpha}$ and $Q\subseteq\mathbb{F}_2^{\beta}$, and let $g : P \to \mathbb{R}$, $h : Q \to \mathbb{R}$ be weights with $|g|,|h|\le1$. Then

$$
\Bigl(\sum_{p\in P}\sum_{q\in Q}g(p)h(q)(-1)^{p^{T}Bq}\Bigr)^2\cdot2^{\operatorname{rank}B}\le|P|\,|Q|\,2^{\alpha}2^{\beta}.
$$

In particular, for the inner product matrix ($B=I$, $\alpha=\beta=n$), every combinatorial rectangle $P\times Q$ satisfies $\bigl|\sum_{P\times Q}(-1)^{\langle p,q\rangle}\bigr|\le\sqrt{|P||Q|2^n}$, so inner product has no monochromatic rectangles of size above $2^n$.

## Proof sketch

Let $M=((-1)^{p^{T}Bq})_{p,q}$. Then $(MM^{T})_{pp'}=2^{\beta}[B^{T}(p+p')=0]$, a block matrix of all-ones blocks of size $2^{\alpha-\operatorname{rank}B}$ scaled by $2^\beta$, so $\|M\|^2=2^{\alpha+\beta-\operatorname{rank}B}$. The sum is $g^{T}Mh$ with $g,h$ supported on $P,Q$, and $|g^{T}Mh|\le\|M\|\,\|g\|\,\|h\|\le\|M\|\sqrt{|P||Q|}$.

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Eyal Kushilevitz, Noam Nisan, "Communication Complexity", Cambridge University Press, 1997.
