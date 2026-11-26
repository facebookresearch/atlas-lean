# Characterization of combined information transfer

**Theorem.** Let $p$ and $q$ be distinct vertices of a [protection graph](take-grant-protection-graphs.md) $G$. Then
[$\mathrm{can{\cdot}know}(p, q, G)$](combined-transfer-and-can-know.md) holds if and only if

1. [$\mathrm{can{\cdot}share}(r, p, q, G)$](can-share-predicate.md) holds, or
2. there is a sequence of subjects $u_1, \dots, u_n$ such that $p = u_1$ or $u_1$ rw-initially spans to $p$; $q = u_n$ or $u_n$ rw-terminally spans to $q$; and for
   every $1 \le i < n$ there is an rwtg-path between $u_i$ and $u_{i+1}$ with an associated word in $B \cup C$.

The proof reorders a witnessing sequence so that all de jure rules precede the de facto rules, and then applies the
[characterization of de facto transfer](characterization-of-de-facto-transfer.md) to the graph reached by the de jure rules.

## Depends on

- [Combined transfer and the can·know predicate](combined-transfer-and-can-know.md)
- [The can·share predicate](can-share-predicate.md)

## Proof depends on

- [Characterization of de facto transfer](characterization-of-de-facto-transfer.md)
- [Characterization of can·share in the take–grant model](can-share-theorem.md)

## Sources

- M. Bishop and L. Snyder, *The Transfer of Information and Authority in a Protection System*, Research Report 166, Department of Computer Science, Yale University, July 1979, <http://nob.cs.ucdavis.edu/~bishop/notes/1979-yalecs-166/yale-166.pdf>: Theorem 5.1 and its proof (pp. 23–27).
