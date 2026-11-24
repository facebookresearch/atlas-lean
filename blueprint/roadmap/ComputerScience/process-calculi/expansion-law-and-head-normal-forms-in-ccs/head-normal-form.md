# Head normal form of a static CCS process

Let the channel names form a type with decidable equality. The head normal form of a static CCS process $P$ is the finite sum $\Sigma h(P)$ of its head summands $h(P)$, that is, the right-associated choice $\alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0)))$ when $h(P) = [(\alpha_1, P_1), \dots, (\alpha_n, P_n)]$, and $0$ when $h(P)$ is empty.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 3, ISBN 978-0-13-115007-2.
