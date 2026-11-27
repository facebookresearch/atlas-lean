# Scott's way-below relation

In a complete lattice $D$ with its Scott topology, $x$ is way below $y$, written $x \ll y$ (Scott writes $x \prec y$), when $y$ lies in the interior of the principal upper set $\{z \mid x \le z\}$ (D. Scott, *Continuous Lattices*, Oxford PRG-7 (1971), §2, definition before Proposition 2.2). Scott's "induced topology" on a complete lattice is the Scott topology: its open sets are the upper sets that are inaccessible by directed suprema. The relation is a transitive approximation relation refining the order: $x \ll y$ implies $x \le y$, and $x \le x' \ll y' \le y$ implies $x \ll y$. It need not be irreflexive: $x \ll x$ holds exactly when the principal upper set of $x$ is Scott-open, that is, when $x$ is compact, as every element of a finite lattice is. In a continuous lattice, for every nonempty directed set $S$, $x \ll \bigsqcup S$ if and only if $x \ll s$ for some $s \in S$ (Proposition 2.2).

## Sources

- D. Scott, *Continuous Lattices*, Technical Monograph PRG-7, Oxford University Computing Laboratory, August 1971, <http://www.cs.ox.ac.uk/files/3229/PRG07.pdf>. This is the pre-publication monograph version of the paper in *Toposes, Algebraic Geometry and Logic*, Lecture Notes in Mathematics 274 (1972), 97–136; theorem numbers here are those of PRG-7.
