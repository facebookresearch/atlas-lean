# Abstract labeled-vertex graph for complementary pivoting

This node collects the abstract labelled-graph interface used for the Lemke–Howson algorithm.

## Expansion

A sound expansion has separate pages for:

1. **Axioms.** A label set $K$ with $\lvert K \rvert = m + n$; for each side $s \in \{1, 2\}$ with $d_1 = m$, $d_2 = n$, a finite vertex set $V_s$, a
   simple graph on $V_s$ and a label map $L_s : V_s \to 2^K$ with (a) $\lvert L_s(v) \rvert = d_s$, (b) distinct vertices have distinct label sets,
   and (c) every vertex has exactly $d_s$ neighbours and, for each label $k$ of $v$, a unique neighbour $v'$ with $L_s(v') \cap L_s(v) = L_s(v) \setminus \{k\}$.
   These per-side conditions play the role of nondegeneracy.
2. **Configurations.** An artificial pair $(x_0, y_0)$ with $L_1(x_0) \cup L_2(y_0) = K$; for a missing label $k$, the pairs with
   $L_1(x) \cup L_2(y) \supseteq K \setminus \{k\}$, and the graph induced on them by pivoting on one side. Labels are kept per side, so a
   configuration is either completely labelled or has exactly one label in $L_1(x) \cap L_2(y)$.
3. **Degree lemma.** Every configuration has degree at most $2$, with degree $1$ exactly at the completely labelled configurations,
   including $(x_0, y_0)$.
4. **Geometric bridge.** For a bimatrix game whose best-response polytopes are simple, their vertices, edges and binding
   inequalities satisfy these axioms (Pritchard, CO 456 Notes 3, Theorem 2 and the label correspondence after it). The bridge states
   which nondegeneracy hypothesis it uses and how it relates to [nondegenerate bimatrix games](is-nondegenerate.md).

## Related topics

- [Bimatrix games and the Lemke–Howson algorithm](README.md)
- [A nondegenerate bimatrix game has an odd number of Nash equilibria](odd-ncard-is-bimatrix-nash.md)

## Sources

- D. Pritchard, CO 456 Game Theory (University of Waterloo, F08), Notes 3: The Lemke–Howson Algorithm, §1: Assumption 2 (simple polytopes), Theorem 2(a)–(c), the correspondence between labels and binding inequalities, and the proof of Claim 1 (configurations, their adjacency, and degrees one and two). <http://ints.io/daveagp/co456/lemke-howson.pdf>
