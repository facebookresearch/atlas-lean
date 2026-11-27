# Four-wise independent random variables

Let $\mu$ be a measure on a measurable space $\Omega$. A family $(\varepsilon_i)_{i \in \iota}$ of real-valued functions on $\Omega$ is four-wise independent under $\mu$ if for every finite set $S \subseteq \iota$ with $|S| \le 4$ the functions $(\varepsilon_i)_{i \in S}$ are mutually independent under $\mu$ (N. Alon, Y. Matias and M. Szegedy, *J. Comput. System Sci.* 58 (1999), proof of Theorem 2.2, where the signs are drawn from an orthogonal array of strength 4).

The source realizes such signs with an explicit set of $O(n^2)$ vectors in $\{-1,1\}^n$ (an orthogonal array of strength 4, from the parity-check matrices of BCH codes), so that the seed takes $O(\log n)$ bits.

## Background

- [Universal hashing](../../data-structures/hashing/universal-hashing/README.md): pairwise-independent hash families, the two-wise analogue used for the same purpose.
