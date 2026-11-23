# The first meeting time from $n$ on attains the envelope conditionally

Let $\mu$ be a finite measure, $(\mathcal{G}_k)$ a filtration, and $(G_k)$ an adapted reward
sequence with every $G_k$ integrable, and let $S$ be the [Snell envelope](snell-envelope.md) with
horizon $N$. Let $n \le N$ and let $\tau_n = \min\{k \in [n, N] : S_k = G_k\}$ be the [first
meeting time from $n$ on](snell-stopping-time-from.md). Then
$S_n = \mathbb{E}[G_{\tau_n} \mid \mathcal{G}_n]$ almost everywhere.

The proof checks $\int_A S_n = \int_A S_{\tau_n}$ for every $A \in \mathcal G_n$: on
$A \cap \{i < \tau_n\} \in \mathcal G_i$ the envelope equals its continuation value
$\mathsf E[S_{i+1} \mid \mathcal G_i]$, so every increment of $S$ up to $\tau_n$ integrates to
zero. Together with the [domination of every conditional stopped
reward](cond-exp-stopped-value-le-snell-envelope.md), this is the content of the book's (1.1.28),
$S_n = \operatorname{ess\,sup}_{n \le \tau \le N} \mathsf E[G_\tau \mid \mathcal G_n]$ with the
supremum attained at $\tau_n$; the essential supremum itself does not appear in the statement.

## Sources

- G. Peskir and A. Shiryaev, *Optimal Stopping and Free-Boundary Problems*, Lectures in Mathematics ETH Zürich, Birkhäuser, 2006, Chapter I, §1.1, Theorem 1.2 (finite horizon), (1.1.10), and (1.1.28).

## Background

- [The Snell envelope dominates every conditional stopped reward](cond-exp-stopped-value-le-snell-envelope.md): the inequality half of (1.1.28).
