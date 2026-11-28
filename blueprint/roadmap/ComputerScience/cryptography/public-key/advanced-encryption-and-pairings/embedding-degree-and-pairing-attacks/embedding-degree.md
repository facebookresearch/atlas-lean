# Embedding degree

For a prime power $q$ and a positive integer $n$ prime to $q$, the embedding degree $k(q,n)$ is the multiplicative order of $q$ modulo $n$; the $n$-th roots of unity lie in $\mathbb{F}_{q^j}^\times$ exactly when $k(q,n)$ divides $j$.

Let $q$ be a prime power and $n\ge1$ an integer with $\gcd(n,q)=1$. The *embedding degree* $k(q,n)$ is the order of the unit $q$ in $(\mathbb{Z}/n\mathbb{Z})^\times$, that is, the least $k\ge1$ with $n\mid q^k-1$ (so $k(q,1)=1$). Let $\mu_n$ be the group of $n$-th roots of unity in an algebraic closure of $\mathbb{F}_q$; it is cyclic of order $n$. **Theorem.** For every integer $j\ge1$,

$$
\mu_n\subseteq\mathbb{F}_{q^j}^\times \iff k(q,n)\mid j .
$$

In particular $\mathbb{F}_{q^{k(q,n)}}$ is the smallest extension of $\mathbb{F}_q$ whose multiplicative group contains $\mu_n$. If $q=p^m$ with $m>1$, the smallest field of characteristic $p$ containing $\mu_n$ is $\mathbb{F}_{p^e}$ with $e$ the order of $p$ modulo $n$, a subfield of $\mathbb{F}_{q^{k(q,n)}}$ that need not contain $\mathbb{F}_q$.

## Depends on

None.

## Proof depends on

None.

## Expansion

$x^n-1$ is separable over $\mathbb{F}_q$ because $n$ is prime to the characteristic, so $\mu_n$ has $n$ elements and is cyclic. The group $\mathbb{F}_{q^j}^\times$ is cyclic of order $q^j-1$, so it contains a subgroup of order $n$, necessarily $\mu_n$, exactly when $n\mid q^j-1$, which holds exactly when the order of $q$ modulo $n$ divides $j$. The last remark applies the same argument with $p$ in place of $q$.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Definition 26.3.7 and Section 26.4.
- A. V. Sutherland, *18.783 Elliptic Curves*, Lecture 23 notes, MIT, Fall 2023, <https://math.mit.edu/classes/18.783/2023/LectureNotes23.pdf>, Section 23.7.
