# Characterization of can·know

**Theorem (Bishop and Snyder).** Let $x$ and $y$ be vertices of a [protection graph](take-grant-protection-graphs.md) $G_0$. Then
[$\mathrm{can{\cdot}know}(x, y, G_0)$](combined-transfer-and-can-know.md) holds if and only if there is a sequence of subjects $u_1, \dots, u_n$ of $G_0$ ($n \ge 1$) such
that

1. $u_1 = x$ or $u_1$ rw-initially spans to $x$;
2. $u_n = y$ or $u_n$ rw-terminally spans to $y$;
3. for every $1 \le i < n$ there is an rwtg-path between $u_i$ and $u_{i+1}$ with an associated word in $B \cup C$, the languages of
   [bridges](tg-paths-islands-spans-and-bridges.md) and [connections](combined-transfer-and-can-know.md).

## Depends on

- [The can·know predicate, rwtg-paths and connections](combined-transfer-and-can-know.md)
- [tg-paths, islands, spans and bridges](tg-paths-islands-spans-and-bridges.md)
- [Take–grant protection graphs](take-grant-protection-graphs.md)

## Sources

- M. Bishop, "Conspiracy and information flow in the take-grant protection model", *Journal of Computer Security* 4(4):331–359, 1996, author copy at <http://nob.cs.ucdavis.edu/bishop/papers/1996-jcs/tgconsp.pdf>: Section 2, Theorem 3 (credited there to M. Bishop and L. Snyder, *Proceedings of the 7th ACM Symposium on Operating Systems Principles*, 1979).
