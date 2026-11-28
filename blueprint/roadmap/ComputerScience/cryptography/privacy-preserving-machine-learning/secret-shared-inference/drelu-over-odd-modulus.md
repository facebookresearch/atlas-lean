# Sign test for additive shares over an odd modulus

Over $\mathbb{Z}_n$ with $n$ odd, call $a$ nonnegative when its lift is below $\lceil n/2\rceil$. For shares with lifts $a_0,a_1\in[0,n)$, $a_0+a_1\equiv a$, and $\mathrm{wrap}=\mathbf 1\{a_0+a_1>n-1\}$, $\mathrm{lt}=\mathbf 1\{a_0+a_1>(n-1)/2\}$, $\mathrm{rt}=\mathbf 1\{a_0+a_1>n+(n-1)/2\}$, $\mathrm{DReLU}(a)$ is $1\oplus\mathrm{lt}$ if $\mathrm{wrap}=0$ and $1\oplus\mathrm{rt}$ if $\mathrm{wrap}=1$.

If $a_0>(n-1)/2$ then $\mathrm{lt}=1$, and if $a_0\le(n-1)/2$ then $\mathrm{rt}=0$, so party 0 knows which of the two tests is constant. In two's-complement rings the sign is a bit of the representation; for odd $n$ it is not, which is why this case split is used. CrypTFlow2's Algorithms 3 and 4 evaluate these tests with [millionaires' comparisons](block-recursive-millionaires-protocol.md).

## Depends on

None.

## Proof depends on

None.

## Expansion

If $a_0+a_1\le n-1$ then $a=a_0+a_1$ as integers and $a$ is nonnegative iff $a_0+a_1\le(n-1)/2$; otherwise $a=a_0+a_1-n$ and the threshold shifts by $n$. The two algorithms are separate protocol pages.

## Sources

- Deevashwer Rathee, Mayank Rathee, Nishant Kumar, Nishanth Chandran, Divya Gupta, Aseem Rastogi, Rahul Sharma, "CrypTFlow2: Practical 2-Party Secure Inference", ACM CCS 2020, DOI 10.1145/3372297.3417274; numbers and equations from the author-deposited arXiv:2010.06457v1: rendered pp. 6–7, §3.3, Algorithms 3 and 4.
