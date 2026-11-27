# Transitions of the expansion of two finite sums

Let the channel names form a type with decidable equality. For a list $s$ of summands (pairs $(\alpha, P)$ of a CCS action and a static CCS process), $\Sigma s$ denotes the right-associated finite choice $\alpha_1.P_1 + (\alpha_2.P_2 + (\cdots + (\alpha_n.P_n + 0)))$ of its entries, with $\Sigma [\,] = 0$. Let $E$ be the expansion of lists $s$ and $t$ of summands. For every CCS action $\alpha$ and every static CCS process $R$, there is a transition $E \xrightarrow{\alpha} R$ in static CCS if and only if one of the following holds:

- there is $P$ with $(\alpha, P)$ an entry of $s$ and $R = P \mid \Sigma t$;
- there is $Q$ with $(\alpha, Q)$ an entry of $t$ and $R = \Sigma s \mid Q$;
- $\alpha = \tau$ and there are entries $(\beta, P)$ of $s$ and $(\gamma, Q)$ of $t$ with $\beta$ and $\gamma$ complementary and $R = P \mid Q$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 3, ISBN 978-0-13-115007-2.
