# Length-space trade-offs in resolution

There are explicit $O(1)$-width CNF formulas that resolution refutes in small space and also in linear length, while every refutation in somewhat smaller space must be superpolynomially or even exponentially long, even in semantic resolution.

Fix $K \ge 1$. Each item gives explicitly constructible CNF formulas $F_n$ of size $\Theta(n)$ and width $O(1)$.

1. **Quadratic trade-offs for constant space.** $F_n$ is refutable in total space $O(1)$; for every monotone $s(n) = O(\sqrt{n})$ there are refutations in simultaneous length $O((n/s(n))^2)$ and total space $O(s(n))$; and every semantic resolution refutation in clause space at most $s(n)$ has length $\Omega((n/s(n))^2)$.
2. **Superpolynomial trade-offs for arbitrarily slowly growing space.** For any $g(n) = \omega(1)$ with $g(n) = O(n^{1/7})$ and any $\epsilon > 0$: $F_n$ is refutable in total space $O(g(n))$, and in simultaneous length $O(n)$ and total space $O((n/g(n)^2)^{1/3})$, but every semantic resolution refutation in clause space $O((n/g(n)^2)^{1/3 - \epsilon})$ has superpolynomial length.
3. **Robust trade-offs for medium space.** $F_n$ is refutable in total space $O(\log^2 n)$, and in length $O(n)$ with total space $O(n / \log n)$, but every semantic resolution refutation in clause space $o(n / \log n)$ has length $n^{\Omega(\log \log n)}$.
4. **Exponential trade-offs for nearly linear space.** For every sufficiently large constant $K'$ there is a constant $K'' \ll K'$ such that $F_n$ has refutations in total space $K'' n / \log n$, and refutations in simultaneous length $O(n)$ and total space $O(n)$, but every semantic resolution refutation in clause space at most $K' n / \log n$ has length $\exp(n^{\Omega(1)})$.

Items 1-3 extend to $k$-DNF resolution for $k \le K$, with the space thresholds replaced by their $(k+1)$-st roots, and all hidden constants depend only on $K$ (and on $\epsilon$ and $g$ in item 2).

## Expansion

The formulas are substituted pebbling formulas $\mathrm{Peb}_G[f]$ with $f$ non-authoritarian (for instance XOR of two variables), for DAG families $G$ with tight trade-offs between pebbling time and space, taken from the pebbling trade-offs of Lengauer and Tarjan and, for item 2, from a construction building on Carlson and Savage. Upper bounds simulate black-white pebblings by resolution; lower bounds apply the substitution theorem, which turns a short small-space refutation of $\mathrm{Peb}_G[f]$ into a resolution refutation of $\mathrm{Peb}_G$ with few downloads in small variable space, and that in turn into a fast pebbling of $G$ in small space, contradicting the pebbling trade-off. Since upper bounds are stated in total space and lower bounds in clause space, the trade-offs hold for both measures.

## Depends on

- [Variable space and total space of resolution refutations](variable-and-total-space.md)
- [Pebbling formulas of directed acyclic graphs](../../resolution-separations-and-supercritical-tradeoffs/pebbling-formula.md)

## Proof depends on

- [Substitution theorem for resolution space](substitution-theorem-for-resolution-space.md)
- [The black-white pebble game](black-white-pebble-game.md)

## Sources

- J. Nordström, "Pebble games, proof complexity, and time-space trade-offs", *Logical Methods in Computer Science* 9(3:15), 2013, doi:10.2168/LMCS-9(3:15)2013, arXiv:1307.3913v3 (Section 4.3: theorems on quadratic trade-offs for constant space, superpolynomial trade-offs for arbitrarily slowly growing space, robust superpolynomial trade-off for medium space, and exponential trade-offs for nearly linear space; Remark following the quadratic trade-off).
- E. Ben-Sasson, J. Nordström, "Understanding space in proof complexity: separations and trade-offs via substitutions", *Innovations in Computer Science (ICS)*, 2011, where these trade-offs were first proved.
