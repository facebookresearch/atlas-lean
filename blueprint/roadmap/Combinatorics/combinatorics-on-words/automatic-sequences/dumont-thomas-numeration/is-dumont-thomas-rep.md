# Dumont–Thomas complement representations

Let $\eta$ map each letter of an alphabet $A$
to a finite word over $A$, extended to finite words by concatenation, with iterates $\eta^j$;
let $u = (u_i)_{i \in \mathbb{Z}}$ be a two-sided word over $A$ and let $p$ be a natural
number. A finite word $w$ of natural-number digits is a Dumont–Thomas complement
representation of an integer $n$ with respect to $\eta$, $u$ and $p$ when one of the following
four conditions holds. Either $n = 0$ and $w$ is the one-digit word $0$; or $n = -1$ and $w$ is
the one-digit word $1$; or $n = N$ for a natural number $N \ge 1$ and there are a natural
number $k$ divisible by $p$ and a $u_0$-admissible sequence $(m_i, a_i)_{0 \le i \le k-1}$
such that the word $m_{k-1} m_{k-2} \cdots m_{k-p}$ is nonempty,
$u_0 u_1 \cdots u_{N-1} = \eta^{k-1}(m_{k-1}) \cdots \eta^0(m_0)$ and $w$ is the digit word
$0, |m_{k-1}|, \ldots, |m_0|$; or $n = -N$ for a natural number $N \ge 2$ and, writing
$L_k = |\eta^k(u_{-1})|$, there are a natural number $k$ divisible by $p$ with $N \le L_k$
and a $u_{-1}$-admissible sequence $(m_i, a_i)_{0 \le i \le k-1}$ such that
$\eta^{p-1}(m_{k-1}) \cdots \eta^0(m_{k-p}) \, a_{k-p} \ne \eta^p(u_{-1})$,
$u_{-L_k} u_{-L_k+1} \cdots u_{-N-1} = \eta^{k-1}(m_{k-1}) \cdots \eta^0(m_0)$ (the empty word
when $N = L_k$) and $w$ is the digit word $1, |m_{k-1}|, \ldots, |m_0|$.

## Sources

- Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Section 4 (definition of Dumont–Thomas complement numeration systems for `ℤ`).
