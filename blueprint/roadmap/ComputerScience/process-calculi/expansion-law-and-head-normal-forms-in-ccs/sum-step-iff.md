# Transitions of a finite sum are its summands

Let the channel names form a type with decidable equality. For a list $s$ of summands (pairs $(\alpha, P)$ of a CCS action and a static CCS process), $\Sigma s$ denotes the right-associated finite choice $\alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0)))$ of its entries, with $\Sigma [\,] = 0$. For every list $s$ of summands, every CCS action $\alpha$ and every static CCS process $P'$, there is a transition $\Sigma s \xrightarrow{\alpha} P'$ in static CCS if and only if $(\alpha, P')$ is an entry of $s$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 3, ISBN 978-0-13-115007-2.
