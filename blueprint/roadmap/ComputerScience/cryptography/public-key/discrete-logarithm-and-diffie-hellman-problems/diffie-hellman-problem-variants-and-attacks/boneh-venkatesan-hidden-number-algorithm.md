# Boneh–Venkatesan algorithm for the hidden number problem

For a prime $p>2^{32}$, $n=2\lceil\sqrt{\log_2p}\rceil$ hidden-number samples with precision $k=\lceil\sqrt{\log_2p}\rceil+\lceil\log_2\log_2p\rceil$ determine $\alpha$ in polynomial time with probability at least $1-2^{-n}$ over the multipliers, using LLL reduction and Babai's nearest-plane algorithm.

Let $(t_i,u_i)$, $1\le i\le n$, be a hidden number problem instance for $\alpha\in\mathbb{F}_p^*$ with precision $k$, and let $L\subseteq\mathbb{R}^{n+1}$ be the lattice spanned by the rows of

$$
B=\begin{pmatrix} p&0&\cdots&0&0\\ 0&p&\cdots&0&0\\ \vdots&&\ddots&&\vdots\\ 0&0&\cdots&p&0\\ t_1&t_2&\cdots&t_n&1/2^{k+1}\end{pmatrix},
$$

with target $u=(u_1,\dots,u_n,0)$. Then $\det L=p^n/2^{k+1}$ and $L$ contains $v_\alpha=(\alpha t_1\bmod p,\dots,\alpha t_n\bmod p,\alpha/2^{k+1})$ with $\|u-v_\alpha\|<\sqrt{n+1}\,p/2^{k+1}$.

**Theorem.** (a) Let $p>2^8$ be prime, $n=2\lceil\sqrt{\log_2p}\rceil$ and $\log_2p-1\ge k>\mu=\tfrac12\sqrt{\log_2p}+3$. With probability at least $1-2^{-n}$ over the independent uniform multipliers $t_1,\dots,t_n$, every $v\in L$ with $\|v-u\|<p/2^{\mu+1}$ has last coordinate $\beta/2^{k+1}$ with $\beta\equiv\alpha\pmod p$. (b) Let $p>2^{32}$, $n=2\lceil\sqrt{\log_2p}\rceil$ and $k=\lceil\sqrt{\log_2p}\rceil+\lceil\log_2\log_2p\rceil$. The algorithm that runs LLL with $\delta=1/4+1/\sqrt2$ on $B$ and Babai's nearest-plane algorithm on $u$, and reads $\alpha$ from the last coordinate of the output, runs in polynomial time in $\log p$ and outputs $\alpha$ with probability at least $1-2^{-n}$ over the multipliers.

## Depends on

- [Hidden number problem](hidden-number-problem.md)
- [The Lenstra–Lenstra–Lovász algorithm](../../../../algebraic-and-numerical-algorithms/lattice-basis-reduction/the-lenstralenstralovasz-algorithm.md)
- [Babai's nearest-plane algorithm](../../../../algebraic-and-numerical-algorithms/nearest-plane-and-lll-potential/babai-nearest-plane-algorithm.md)

## Proof depends on

None.

## Expansion

(a) A close vector with $\beta\not\equiv\alpha$ forces $|(\beta-\alpha)t_i\bmod p|<p/2^\mu$ for all $i$, with the residue measured by its centered representative; for fixed $\gamma=\beta-\alpha\ne0$ each $t_i$ satisfies this with probability $<4/2^\mu$, and a union bound over the $p-1$ values of $\beta$ gives failure probability $<2^{\log_2p+2n}/2^{\mu n}\le2^{-n}$ since $\mu n\ge\log_2p+3n$. (b) Scale the lattice and target by $2^{k+1}$ to work with integer vectors. For a basis that is LLL-reduced with $\delta=1/4+1/\sqrt2$, Babai's nearest-plane algorithm returns $v$ with $\|v-w\|\le(1.6)\,2^{d/4}\|x-w\|$ for every lattice vector $x$, in dimension $d$ (Galbraith, Theorem 18.1.7, which prints a strict inequality; the strict form fails when $w$ itself lies in the lattice). With $d=n+1$, $w=u$ and $x=v_\alpha$, and the strict bound $\|u-v_\alpha\|<\sqrt{n+1}\,p/2^{k+1}$, this gives $\|v-u\|<(1.6)\,2^{(n+1)/4}\sqrt{n+1}\,p/2^{k+1}$, which is below $p/2^{\mu+1}$ for the stated $k$, and (a) applies. Prerequisite still to add: this non-strict nearest-plane bound for $\delta=1/4+1/\sqrt2$, which is stronger than the $\delta=3/4$ bound $2^{d/2}$.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Definition 21.7.7, Lemma 21.7.8, Theorem 21.7.9, Corollary 21.7.10 and Theorem 18.1.7.
