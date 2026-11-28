# Non-adjacent form

A non-adjacent form (NAF) of a positive integer $a$ is a signed binary expansion $a=\sum_i a_i2^i$ with digits in $\{-1,0,1\}$ and no two adjacent nonzero digits; every positive integer has one, computed right to left.

Let $a\in\mathbb{Z}_{\ge1}$. A representation

$$
a=\sum_{i=0}^{l}a_i2^i,\qquad a_i\in\{-1,0,1\},
$$

is a *non-adjacent form* if $a_ia_{i+1}=0$ for all $0\le i<l$; if $a_l\ne0$ its length is $l+1$. Negating all digits gives a NAF of $-a$. A NAF of $a$ is produced by the right-to-left algorithm: while $a\ne0$, if $a$ is even emit the digit $0$, otherwise emit $a_i\in\{-1,1\}$ with $a_i\equiv a\pmod 4$; then replace $a$ by $(a-a_i)/2$. Equivalently, subtracting the binary digits of $a$ from those of $3a$ position by position, without carries, and discarding the least significant digit gives a NAF of $a$.

## Depends on

None.

## Proof depends on

None.

## Expansion

The algorithm terminates because $|a|$ decreases, and its output is a NAF: when $a$ is odd the emitted digit makes $(a-a_i)/2$ even, so the next digit is $0$ (Galbraith, Exercise 11.1.2). The $(3a)-a$ characterization is Galbraith's Lemma 11.1.4, proved by tracking the carries of the binary addition $3a=2a+a$. Signed expansions are used for scalar multiplication on elliptic curves because negating a point is cheap.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Definition 11.1.1, Algorithm 6, Exercise 11.1.2, Lemma 11.1.4 and Exercise 11.1.7.
