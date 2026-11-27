# Length-space trade-offs in resolution

There are $O(1)$-width CNF formulas, explicitly constructible except in the nearly linear space regime, that resolution refutes in small space and also in linear length, while every refutation in somewhat smaller space must be superpolynomially or even exponentially long, even in semantic resolution.

Fix $K \ge 1$. Items 1-3 give explicitly constructible CNF formulas $F_n$ of size $\Theta(n)$ and width $O(1)$; item 4 gives CNF formulas $F_n$ of size $\Theta(n)$ and width $O(1)$, whose existence the sources assert without claiming an explicit construction.

1. **Quadratic trade-offs for constant space.** $F_n$ is refutable in total space $O(1)$; for every monotone $s(n) = O(\sqrt{n})$ there are refutations in simultaneous length $O((n/s(n))^2)$ and total space $O(s(n))$; and every semantic resolution refutation in clause space at most $s(n)$ has length $\Omega((n/s(n))^2)$.
2. **Superpolynomial trade-offs for arbitrarily slowly growing space.** For any $g(n) = \omega(1)$ with $g(n) = O(n^{1/7})$ and any $\epsilon > 0$: $F_n$ is refutable in total space $O(g(n))$, and in simultaneous length $O(n)$ and total space $O((n/g(n)^2)^{1/3})$, but every semantic resolution refutation in clause space $O((n/g(n)^2)^{1/3 - \epsilon})$ has superpolynomial length.
3. **Robust trade-offs for medium space.** $F_n$ is refutable in total space $O(\log^2 n)$, and in length $O(n)$ with total space $O(n / \log n)$, but every semantic resolution refutation in clause space $o(n / \log n)$ has length $n^{\Omega(\log \log n)}$.
4. **Exponential trade-offs for nearly linear space.** For every sufficiently large constant $K'$ there are such formulas $F_n$ and a constant $K'' \ll K'$ such that $F_n$ has refutations in total space $K'' n / \log n$, and refutations in simultaneous length $O(n)$ and total space $O(n)$, but every semantic resolution refutation in clause space at most $K' n / \log n$ has length $\exp(n^{\Omega(1)})$.

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

- J. Nordström, "Pebble games, proof complexity, and time-space trade-offs", *Logical Methods in Computer Science* 9(3:15), 2013, doi:10.2168/LMCS-9(3:15)2013, arXiv:1307.3913v3 (Section 4.3: Theorems 4.15, 4.17 and 4.18, which state explicitly constructible formulas, and Theorem 4.19, the exponential trade-off for nearly linear space, which states only that such formulas exist; Remark following the quadratic trade-off).
- E. Ben-Sasson, J. Nordström, "Understanding space in proof complexity: separations and trade-offs via substitutions", *Innovations in Computer Science (ICS)*, 2011, 401-416, where these trade-offs were first proved; numbering from the full version read, ECCC TR10-125 (Theorems 2.6, 2.8 and 2.9 with explicitly constructible formulas, and Theorem 2.10, which states "there are CNF formulas").
