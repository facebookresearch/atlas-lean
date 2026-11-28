# Length-space trade-offs in resolution

There are explicitly constructible $O(1)$-width CNF formulas that resolution refutes in small space and also in linear length, while every refutation in somewhat smaller space must be superpolynomially or even exponentially long, even in semantic resolution.

Fix $K \ge 1$. Each item gives explicitly constructible CNF formulas $F_n$ of size $\Theta(n)$ and width $O(1)$, that is, the $n$th formula is produced from $1^n$ in polynomial time.

1. **Quadratic trade-offs for constant space.** $F_n$ is refutable in total space $O(1)$; for every monotone $s(n) = O(\sqrt{n})$ there are refutations in simultaneous length $O((n/s(n))^2)$ and total space $O(s(n))$; and every semantic resolution refutation in clause space at most $s(n)$ has length $\Omega((n/s(n))^2)$.
2. **Superpolynomial trade-offs for arbitrarily slowly growing space.** For any $g(n) = \omega(1)$ with $g(n) = O(n^{1/7})$ and any $\epsilon > 0$: $F_n$ is refutable in total space $O(g(n))$, and in simultaneous length $O(n)$ and total space $O((n/g(n)^2)^{1/3})$, but every semantic resolution refutation in clause space $O((n/g(n)^2)^{1/3 - \epsilon})$ has superpolynomial length.
3. **Robust trade-offs for medium space.** $F_n$ is refutable in total space $O(\log^2 n)$, and in length $O(n)$ with total space $O(n / \log n)$, but every semantic resolution refutation in clause space $o(n / \log n)$ has length $n^{\Omega(\log \log n)}$.
4. **Exponential trade-offs for nearly linear space.** For every sufficiently large constant $K'$ there are such formulas $F_n$ and a constant $K'' \ll K'$ such that $F_n$ has refutations in total space $K'' n / \log n$, and refutations in simultaneous length $O(n)$ and total space $O(n)$, but every semantic resolution refutation in clause space at most $K' n / \log n$ has length $\exp(n^{\Omega(1)})$.

Items 1-3 extend to $k$-DNF resolution for $k \le K$, with the same syntactic resolution upper bounds and the following semantic formula-space lower-bound thresholds: in item 1, every semantic $k$-DNF resolution refutation in formula space at most $s(n)$ has length $\Omega((n/s(n)^{k+1})^2)$; in item 2, every one in formula space $O((n/g(n)^2)^{1/(3(k+1)) - \epsilon})$ has superpolynomial length; in item 3, every one in formula space $o((n/\log n)^{1/(k+1)})$ has length $n^{\Omega(\log \log n)}$. All hidden constants depend only on $K$ (and on $\epsilon$ and $g$ in item 2).

## Expansion

The formulas are substituted pebbling formulas $\mathrm{Peb}_G[f]$ with $f$ non-authoritarian (for instance XOR of two variables), for DAG families $G$ with tight trade-offs between pebbling time and space, taken from the pebbling trade-offs of Lengauer and Tarjan and, for item 2, from a construction building on Carlson and Savage. Upper bounds simulate black-white pebblings by resolution; lower bounds apply the substitution theorem, which turns a short small-space refutation of $\mathrm{Peb}_G[f]$ into a resolution refutation of $\mathrm{Peb}_G$ with few downloads in small variable space, and that in turn into a fast pebbling of $G$ in small space, contradicting the pebbling trade-off. Since upper bounds are stated in total space and lower bounds in clause space, the trade-offs hold for both measures.

## Depends on

- [Variable space and total space of resolution refutations](variable-and-total-space.md)
- [Pebbling formulas of directed acyclic graphs](../../resolution-separations-and-supercritical-tradeoffs/pebbling-formula.md)

## Proof depends on

- [Substitution theorem for resolution space](substitution-theorem-for-resolution-space.md)
- [The black-white pebble game](black-white-pebble-game.md)

## Sources

- J. Nordström, "Pebble games, proof complexity, and time-space trade-offs", *Logical Methods in Computer Science* 9(3:15), 2013, doi:10.2168/LMCS-9(3:15)2013, arXiv:1307.3913v3 (Section 4.3: Theorems 4.15, 4.17, 4.18 and 4.19, the exponential trade-off for nearly linear space; Remark following the quadratic trade-off). The statement of Theorem 4.19 omits the word "explicitly", which the full version below supplies.
- E. Ben-Sasson, J. Nordström, "Understanding space in proof complexity: separations and trade-offs via substitutions", *Innovations in Computer Science (ICS)*, 2011, 401-416, where these trade-offs were first proved; numbering from the full version read, ECCC TR10-125 (Theorems 2.6, 2.8, 2.9 and 2.10; Section 2.3, p. 8: "We reiterate that all of our results are for explicitly constructible formulas"; Section 7.1, p. 48: the trade-off results "are stated for explicitly constructible formulas"; and Lemma 7.12, p. 55, the Lengauer-Tarjan graphs used in the proof of Theorem 2.10, which gives "an explicitly constructible single-sink DAG". The statement of Theorem 2.10 itself writes "there are CNF formulas").
