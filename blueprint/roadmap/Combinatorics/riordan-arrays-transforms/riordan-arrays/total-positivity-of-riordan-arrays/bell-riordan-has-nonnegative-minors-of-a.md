# Bell-type Riordan arrays with a Pólya frequency A-sequence are totally positive

Let $g$
be a formal power series over $\mathbb{R}$ with $g(0) \neq 0$, write $[x^n]F$ for the coefficient
of $x^n$ in a power series $F$, and let $D = (d_{n,k})_{n,k \ge 0}$ be the Bell-type Riordan array
$(g(x), x g(x))$, with entries $d_{n,k} = [x^n]\, g(x) (x g(x))^k$. Let $(a_j)_{j \ge 0}$ be a
real sequence, the $A$-sequence of $D$, such that for all $n, k \ge 0$

$$d_{n+1,k+1} = \sum_{j=0}^{n} a_j\, d_{n,k+j}.$$

If $(a_j)$ is a Pólya frequency sequence, that is, every minor of its lower Toeplitz matrix
(whose entry in row $n$ and column $k$ is $a_{n-k}$ for $k \le n$ and $0$ otherwise) is
nonnegative, then $D$ is totally positive: every minor of $D$ is nonnegative.

The sum stops at $j = n$ because $d_{n,m} = 0$ for $m > n$.

## Sources

- Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Proposition 5.
