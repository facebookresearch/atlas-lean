# Exact division of two additive shares by a public integer

For additive shares $a_0+a_1\equiv a\pmod n$ and a public integer $0<d<n$, the signed quotient satisfies $\mathrm{rdiv}(a,d)\equiv\mathrm{rdiv}(a_0,d)+\mathrm{rdiv}(a_1,d)+\mathrm{corr}\cdot n^1+1-C-B\pmod n$, where $n=n^1d+n^0$ and $\mathrm{corr},B,C$ are integers determined by the shares' signs and low-order remainders.

Let $\mathrm{idiv}$ be integer division rounding the quotient toward $-\infty$. For $x\in\mathbb{Z}_n$ with unsigned lift $x_u\in\{0,\dots,n-1\}$, let $n'=\lceil n/2\rceil$ and $\mathrm{rdiv}(x,d)=\mathrm{idiv}(x_u-\mathbf 1\{x_u\ge n'\}n,\,d)\bmod n$. Let $n=n^1d+n^0$ with $0\le n^0<d$; let $a_u,a_0,a_1$ be the lifts of $a$ and of the shares, and $a_b=a_b^1d+a_b^0$ with $0\le a_b^0<d$. Define

$$
\mathrm{corr}=\begin{cases}-1&a_u\ge n',\ a_0<n',\ a_1<n',\\ 1&a_u<n',\ a_0\ge n',\ a_1\ge n',\\ 0&\text{otherwise,}\end{cases}
$$

$A=a_0^0+a_1^0-(\mathbf 1\{a_0\ge n'\}+\mathbf 1\{a_1\ge n'\}-\mathrm{corr})n^0$, $B=\mathrm{idiv}(a_0^0-\mathbf 1\{a_0\ge n'\}n^0,d)+\mathrm{idiv}(a_1^0-\mathbf 1\{a_1\ge n'\}n^0,d)$ and $C=\mathbf 1\{A<d\}+\mathbf 1\{A<0\}+\mathbf 1\{A<-d\}$. Then

$$
\mathrm{rdiv}(a_0,d)+\mathrm{rdiv}(a_1,d)+(\mathrm{corr}\cdot n^1+1-C-B)\equiv\mathrm{rdiv}(a,d)\pmod n .
$$

## Depends on

None.

## Proof depends on

None.

## Expansion

The signed lift of $a$ minus the sum of the signed lifts of the shares is exactly $\mathrm{corr}\cdot n$ (App. C). Expanding each signed lift with $a_b=a_b^1d+a_b^0$ and $n=n^1d+n^0$ leaves the remainder sum $A\in[-2d+2,2d-2]$, for which $\mathrm{idiv}(A,d)=1-C$. Each summand of $B$ and each $\mathrm{rdiv}(a_b,d)$ depends on one share only; the protocols that compute shares of the remaining terms (§4.2, App. D) are separate.

## Sources

- Deevashwer Rathee, Mayank Rathee, Nishant Kumar, Nishanth Chandran, Divya Gupta, Aseem Rastogi, Rahul Sharma, "CrypTFlow2: Practical 2-Party Secure Inference", ACM CCS 2020, DOI 10.1145/3372297.3417274; numbers and equations from the author-deposited arXiv:2010.06457v1: rendered pp. 7–8 and 16, §4.1, Equation (2), Theorem 4.1 and Appendix C (Table 8).
