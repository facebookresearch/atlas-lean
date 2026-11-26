# Finite sum of a list of summands

For a finite list $s = [(\alpha_1, P_1), \dots, (\alpha_n, P_n)]$ of summands, each a CCS action paired with a static CCS process, the finite sum $\Sigma s$ is the static CCS process defined by $\Sigma [\,] = 0$ and $\Sigma ((\alpha, P) :: s) = \alpha.P + \Sigma s$, that is,

$$\Sigma s = \alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0))).$$

In particular a one-element list gives $\alpha.P + 0$, not $\alpha.P$ itself.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 3, ISBN 978-0-13-115007-2.
