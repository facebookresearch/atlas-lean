# Density Hales–Jewett theorem

Write $[k] = \{0, 1, \dots, k - 1\}$. A combinatorial line in
$[k]^N$ is given by a nonempty set of free coordinates and a fixed value in $[k]$ at every other
coordinate; its $k$ points are obtained by giving all free coordinates a common value $a \in [k]$.
For every natural number $k \ge 2$ and every real $\delta > 0$ there is a natural number $N$ such
that every set $A \subseteq [k]^N$ with $\delta k^N \le |A|$ contains all $k$ points of some
combinatorial line in $[k]^N$.

Proof: We follow the density-increment route of Dodos–Kanellopoulos–Tyros, with the binary
case supplied by Sperner's theorem and the Graham–Rothschild theorem for lines.

## Sources

- H. Furstenberg and Y. Katznelson, J. Anal. Math. 57 (1991) and Hales-Jewett, Trans. AMS 106 (1963); Lean states finitary density form over `Fin N → Fin k` with coloring version as corollary.
