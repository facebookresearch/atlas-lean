# Rounding-corrected integer decomposition of real-valued masses

Let $a_1 < a_2 < \dots < a_n$ be positive real element masses and let $[l, u] \subset \mathbb{R}_{>0}$ be a mass interval (for a measured monoisotopic mass $M_0$ with accuracy $\varepsilon$, $l = M_0 - \varepsilon$, $u = M_0 + \varepsilon$). A **decomposition** is a vector $c = (c_1, \dots, c_n) \in \mathbb{Z}_{\ge 0}^n$ with

$$l \le \sum_{j=1}^{n} a_j c_j \le u ,$$

that is, a solution of an integer knapsack (money-changing) equation with real coefficients.

Fix a blow-up factor $b > 0$ (precision $1/b$), round $a_j' := \lceil b a_j \rceil \in \mathbb{Z}_{>0}$, and define the relative rounding errors

$$\Delta_j := \frac{\lceil b a_j \rceil - b a_j}{a_j} \in [0, 1/a_j), \qquad \Delta := \max_j \Delta_j .$$

**Claim.** Every real decomposition $c$ of $[l, u]$ satisfies

$$\lceil b l \rceil \;\le\; \sum_{j=1}^{n} a_j' c_j \;\le\; \lfloor b u + \Delta u \rfloor .$$

Hence enumerating all integer decompositions over $a_1', \dots, a_n'$ of every integer in $[\lceil bl \rceil, \lfloor bu + \Delta u \rfloor]$ and discarding those that fail the real-valued inequality returns exactly the real decompositions of $[l, u]$: there are no false negatives, and false positives are removed by one check each. The bound is tight.

Compared with decomposing the $(u - l)b$ integers of the naive rounded interval, the correction adds only about $\Delta u$ integers, independent of the interval width. For the elements CHNOPS and $b = 10^5$, $\Delta = \Delta_{\mathrm{H}} \approx 0.4929$, so at $M_0 = 1000$ Da about $492$ extra integers are decomposed.

## Expansion

Lower bound: $a_j' \ge b a_j$ gives $\sum a_j' c_j \ge b \sum a_j c_j \ge b l$, and the left side is an integer. Upper bound: $a_j' = b a_j + \Delta_j a_j \le (b + \Delta) a_j$, so $\sum a_j' c_j \le (b + \Delta) \sum a_j c_j \le bu + \Delta u$, and again the left side is an integer.

The integer instances are solved with an **extended residue table**: for integer masses $a_1' \le \dots \le a_n'$, entry $\mathrm{ER}(r, i)$ for $0 \le r < a_1'$ is the smallest integer congruent to $r$ modulo $a_1'$ that is decomposable over $a_1', \dots, a_i'$. The table takes $O(n a_1')$ time and space to build, and all decompositions of a query $m$ are generated recursively in $O(n a_1' \gamma(m))$ time, where $\gamma(m)$ is the number of decompositions; the table never prunes a branch that leads to a solution. Because $\gamma(m)$ for coprime integer masses grows like a polynomial of degree $n - 1$ in $m$, output size rather than $m$ dominates the cost.

## Sources

- S. Böcker, M. C. Letzel, Zs. Lipták, A. Pervukhin, "SIRIUS: decomposing isotope patterns for metabolite identification", Bioinformatics 25 (2009) 218–224, Sections 3.1 (real-valued decompositions) and 3.2 (integer decompositions), <https://doi.org/10.1093/bioinformatics/btn603> (PMC2639009).
