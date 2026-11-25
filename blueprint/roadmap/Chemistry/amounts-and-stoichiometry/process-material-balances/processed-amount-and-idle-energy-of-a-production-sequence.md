# Processed amount and idle energy of a production sequence

Let $0 = t_0 < t_1 < \dots < t_m = T$ partition a production period, let the achieved rate be a constant $r_k \ge 0$ on
$(t_{k-1}, t_k)$, and let the cumulative processed amount $Q : [0, T] \to \mathbb{R}$ be continuous with $Q'(t) = r_k$ on each
open interval. Then

$$Q(T) - Q(0) = \sum_{k=1}^m r_k\,(t_k - t_{k-1}),$$

by the fundamental theorem of calculus on each interval and telescoping; for instance rate $2$ on $[0, 1]$ and rate $5$ on
$[1, 3]$ give $12$. If nonnegative good and scrap amounts $G, S$, on the same material and time basis, satisfy
$G + S = Q(T) - Q(0)$, each is at most the processed amount. If the power drawn $P$ is integrable on $[0, T]$ with
$P \ge P_{\mathrm{idle}} \ge 0$ on the intervals with $r_k = 0$ and $P \ge 0$ elsewhere, the energy satisfies
$\int_0^T P\,dt \ge P_{\mathrm{idle}}$ times the total idle time, even when nothing is produced. Constitutive models of machining,
forming or additive processes, and tool life, are outside this result.

## Depends on

## Proof depends on

## Sources

- OpenStax, *Calculus Volume 1*, Section 5.3, the Fundamental Theorem of Calculus, Part 2, <https://openstax.org/books/calculus-volume-1/pages/5-3-the-fundamental-theorem-of-calculus>.
