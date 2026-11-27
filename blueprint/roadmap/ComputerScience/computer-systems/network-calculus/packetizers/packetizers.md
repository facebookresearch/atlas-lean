# Packetizers

A *sequence of cumulative packet lengths* is a wide-sense increasing sequence $L = (L(0) = 0, L(1), L(2), \dots)$ with $L(n) \to \infty$ and $l_{\max} = \sup_n \{L(n + 1) - L(n)\} < \infty$; $L(n) - L(n - 1)$ is the length of the $n$-th packet. For real $x$ let

$$
P^L(x) = \sup_{n \in \mathbb N} \{L(n)\,\mathbf 1_{\{L(n) \le x\}}\},
$$

so for $x \ge 0$, $P^L(x) = L(k)$ with $k = \max\{j : L(j) \le x\}$: the largest cumulative packet length entirely contained in $x$. (With packets of length $0$ allowed, $L(n) \le x < L(n + 1)$ need not hold for every $n$ with $P^L(x) = L(n)$: for $L = (0, 1, 1, 2, \dots)$ and $x = 1$, $P^L(x) = L(1)$ but $L(2) = 1$.) An *$L$-packetizer* is the system that transforms an input [cumulative function](../cumulative-flows-backlog-and-virtual-delay.md) $R(t)$ into $P^L(R(t))$, and a flow is *$L$-packetized* if $P^L(R(t)) = R(t)$ for all $t$. The function $P^L$ is right-continuous, isotone and idempotent, and $x - l_{\max} < P^L(x) \le x$ for $x \ge 0$ (cumulative functions are nonnegative); with unit packets, $P^L(x) = \lfloor x \rfloor$ for $x > 0$. Among all $L$-packetized flows $x \le R$, the flow $P^L(R)$ is the largest.

## Depends on

- [Cumulative flows, backlog and virtual delay](../cumulative-flows-backlog-and-virtual-delay.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.7.2, Definitions 1.7.1–1.7.4, equations (1.19)–(1.22) and the properties listed after Definition 1.7.4.
