# Dense bipartite Ruzsa-Szemerédi graphs from Behrend's progression-free sets

There is an absolute constant $c > 0$ such that for every integer $N \ge 2$ there exists a bipartite $(r, t)$-Ruzsa–Szemerédi graph with $3N$ vertices on each side, $t = N$ induced matchings and

$$
r \ge N e^{-c\sqrt{\ln N}}.
$$

Explicitly: if $A \subseteq \{1, \dots, N\}$ contains no non-trivial three-term arithmetic progression, then the bipartite graph with sides $L = R = \{1, \dots, 3N\}$ and matchings $M_x = \{(x + a, \, x + 2a) : a \in A\}$ for $x \in \{1, \dots, N\}$ is an $(|A|, N)$-Ruzsa–Szemerédi graph.

## Proof sketch

Each $M_x$ is a matching since $a \mapsto x + a$ and $a \mapsto x + 2a$ are injective, and distinct $x$ give disjoint matchings. If some edge of $M_y$ joined the left endpoint $x + a$ and the right endpoint $x + 2b$ of edges of $M_x$, then $x + a = y + c$ and $x + 2b = y + 2c$ for some $c \in A$, so $a + c = 2b$; progression-freeness forces $a = b = c$ and hence $y = x$, proving inducedness. Behrend's construction of a progression-free set of size $N e^{-c\sqrt{\ln N}}$ (points of a large sphere in a cube, read in a large base) finishes the bound.

## Depends on

- [Ruzsa-Szemerédi graphs: edge sets partitioned into large induced matchings](ruzsa-szemeredi-graphs.md)

## Proof depends on

- [Sets of naturals without three-term progressions](../../../../Combinatorics/additive-combinatorics/progressions-dense-sets/arithmetic-progressions-and-progression-free-set/is-apof-length-free-three.md)
- [Behrend's lemma: some sphere contains many lattice points of a cube](../../../../Combinatorics/additive-combinatorics/progressions-dense-sets/bounds-for-roth-numbers/behrend-large-sphere.md)

## Sources

- Imre Z. Ruzsa, Endre Szemerédi, "Triple systems with no six points carrying three triangles", Combinatorics (Proc. Fifth Hungarian Colloq., Keszthely 1976), Colloq. Math. Soc. János Bolyai 18 (1978).
- Felix A. Behrend, "On sets of integers which contain no three terms in arithmetical progression", Proc. Nat. Acad. Sci. USA 32 (1946).
