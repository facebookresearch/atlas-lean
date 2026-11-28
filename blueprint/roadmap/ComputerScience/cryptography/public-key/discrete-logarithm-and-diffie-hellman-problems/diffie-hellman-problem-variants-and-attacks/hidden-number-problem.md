# Hidden number problem

The hidden number problem asks for an unknown $\alpha\in\mathbb{F}_p^*$ given independent uniform multipliers $t_i$ and approximations $u_i$ of $\alpha t_i\bmod p$ with absolute error less than $p/2^{k+1}$.

Let $p$ be an odd prime and $k\in\mathbb{R}_{>1}$. For an integer $x$, write $\mathrm{MSB}_k(x)$ for any integer $u$ with $|x-u|<p/2^{k+1}$. Let $\alpha\in\mathbb{F}_p^*$ and let $t_1,\dots,t_n$ be drawn independently and uniformly from $\mathbb{F}_p^*$. The *hidden number problem* (HNP) is: given

$$
(t_i,\ u_i)\quad\text{with}\quad u_i=\mathrm{MSB}_k(\alpha t_i\bmod p),\qquad 1\le i\le n,
$$

compute $\alpha$. Here $\alpha t_i\bmod p$ denotes the representative in $\{0,\dots,p-1\}$, and the $u_i$ may be any integers satisfying the error bound.

In a different model, where an oracle returns exact information for multipliers chosen adaptively, the problem is easy. Here, for $x\in\{1,\dots,p-1\}$, the exact bit $\mathrm{MSB}_1(x)$ is $0$ if $x<p/2$ and $1$ otherwise, that is $\lfloor2x/p\rfloor$; it is not in general the leading bit of the binary representation of $x$, and it is distinct from the approximation $\mathrm{MSB}_k$ above, defined for $k>1$. With a perfect oracle for $\mathrm{MSB}_1(\alpha t\bmod p)$, $\alpha$ is found with $O(\log p)$ queries, and with a perfect oracle for the least significant bit of $\alpha t\bmod p$, with $O(\log^2p)$ queries.

## Depends on

None.

## Proof depends on

None.

## Expansion

The two adaptive statements are Galbraith's Lemmas 21.7.3 and 21.7.5 (left as exercises there). The non-adaptive version with independent uniform multipliers is the one solved by Boneh and Venkatesan with lattice reduction.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Section 21.7.1, Definition 21.7.2, Lemmas 21.7.3 and 21.7.5.
