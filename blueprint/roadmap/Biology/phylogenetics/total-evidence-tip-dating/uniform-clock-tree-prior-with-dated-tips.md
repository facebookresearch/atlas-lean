# Uniform clock-tree prior with dated tips

Let a clock tree have $n \ge 3$ labelled tips with ages $0 \le a_1 \le a_2 \le \dots \le a_n$ (age measured backward from the present; extant tips have age $0$, fossil tips positive ages), $n - 2$ non-root interior nodes, and a root of age $r$. The uniform clock-tree prior generates a tree as follows:

1. draw each tip age independently from its own prior $f_i$ (a point mass at $0$ for extant tips) and sort;
2. draw the root age $r$ from a density $h$ conditioned on $r > a_n$;
3. draw $x_i \sim \mathrm{Uniform}(a_{i+1}, r)$ independently for $i = 1, \dots, n-2$ and sort them into interior node ages $t_{(1)} < \dots < t_{(n-2)}$;
4. visiting interior nodes from youngest to oldest, merge a uniformly random pair of the lineages present at that age; the last two lineages merge at the root.

For a ranked tree $\tau$ with interior node ages $t_{(1)} < \dots < t_{(n-2)} < r$, let $s_\ell = \#\{i \le n-2 : a_{i+1} < t_{(\ell)}\}$ be the number of uniform draws whose interval contains $t_{(\ell)}$, and let $k_\ell$ be the number of lineages present just below age $t_{(\ell)}$. Then, given the tip ages, the density of $\tau$ is

$$p(\tau \mid a) \;=\; \frac{h(r)}{\int_{a_n}^{\infty} h(u)\,du} \;\prod_{i=1}^{n-2} \frac{1}{r - a_{i+1}} \;\prod_{\ell=1}^{n-2} \frac{s_\ell - \ell + 1}{\binom{k_\ell}{2}},$$

and it vanishes unless $s_\ell \ge \ell$ for all $\ell$, which says that at each age the number of interior nodes below it is less than the number of tips below it. With all tips extant ($a_i = 0$), this reduces to the classical uniform prior on ranked clock trees: node ages uniform on $(0, r)$ given the root age, and a uniform ranked topology.

## Expansion

The vector $x$ has density $\prod_i (r - a_{i+1})^{-1}$ on its box. The sorted vector has density equal to that value times the number of assignments of the sorted ages to the $n-2$ draws that respect the intervals. Assign ages from youngest to oldest: $t_{(\ell)}$ may go to any of the $s_\ell$ draws whose interval contains it, except the $\ell - 1$ already used by younger ages, all of which also contain $t_{(\ell)}$ because $s$ is nondecreasing. This gives the factor $\prod_\ell (s_\ell - \ell + 1)$. Step 4 contributes $1/\binom{k_\ell}{2}$ per interior node. Grouping nodes by the intervals between successive tip ages gives the per-interval factors $(k_j - 1)!/(k_j - 1 - m_j)!$ of the source, where $m_j$ nodes fall among $k_j$ lineages; "subtracting one" reflects that $k$ lineages allow only $k - 1$ mergers. This prior avoids the birth–death model's assumptions about fossilization and extant sampling fractions, which are rarely known. In the hymenopteran case study, total-evidence dating with 45 fossil tips placed the origin of Hymenoptera in the Carboniferous, about 309 million years ago (95% interval 291–347 million years ago).

## Sources

- F. Ronquist, S. Klopfstein, L. Vilhelmsen, S. Schulmeister, D. L. Murray, A. P. Rasnitsyn, "A total-evidence approach to dating with fossils, applied to the early radiation of the Hymenoptera", *Systematic Biology* 61(6) (2012) 973–999, Materials and Methods, subsection on the tree prior for total-evidence dating (uniform prior on clock trees with terminals of different ages), <https://doi.org/10.1093/sysbio/sys058> (PMC3478566).
