# Every static CCS process is strongly bisimilar to its head normal form

Let the channel names form a type with decidable equality. Every static CCS process $P$ is strongly bisimilar, in the labelled transition system of static CCS, to its head normal form $\Sigma h(P)$. Here the head summands $h(P)$ of a static CCS process $P$ are defined by recursion on $P$: $h(0) = [\,]$; $h(\alpha.P) = [(\alpha, \Sigma h(P))]$; $h(P + Q) = h(P) \mathbin{+\!\!+} h(Q)$; $h(P \mid Q)$ is the list of expansion summands of $h(P)$ and $h(Q)$; $h(P \setminus L)$ is $h(P)$ restricted by $L$; and $h(P[f])$ is $h(P)$ relabelled by $f$. The head normal form of $P$ is $\Sigma h(P)$, where $\Sigma s$ is the right-associated finite choice $\alpha_1.P_1 + (\cdots + (\alpha_n.P_n + 0))$ of a list $s$ of summands.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 3, ISBN 978-0-13-115007-2.
