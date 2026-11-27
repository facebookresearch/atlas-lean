# k-unique maps composed with simple tabulation are k-wise independent

Let $\Psi$ be a finite alphabet and $f : U \to \Psi^d$. Call $f$ *$k$-unique* if every nonempty set $S \subseteq U$ with $|S| \le k$ has a unique output position character: some $x_0 \in S$ and $j \in \{1, \dots, d\}$ with $f(x_0)_j \ne f(x)_j$ for all $x \in S \setminus \{x_0\}$. Let $r_1, \dots, r_d : \Psi \to \{0,1\}^M$ be independent uniformly random tables and define the simple tabulation $g(y) = r_1(y_1) \oplus \cdots \oplus r_d(y_d)$ for $y \in \Psi^d$. If $f$ is $k$-unique, then $g \circ f : U \to \{0,1\}^M$ is $k$-wise independent (over the random tables).

## Proof sketch

Induct on $|S|$. Pick $x_0$ and $j$ with a unique character $f(x_0)_j$; the table entry $r_j(f(x_0)_j)$ is used by $x_0$ and no other element of $S$. Conditioning on all other table entries, $g(f(x_0))$ is uniform and independent of the values on $S \setminus \{x_0\}$, which are $(|S|-1)$-wise independent by induction.

## Depends on

- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)

## Sources

- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science, 2013 (Lemma 2, proved in Appendix A, with each table only $k$-wise independent); arXiv:1311.3121.
- A. Siegel, "On Universal Classes of Extremely Random Constant-Time Hash Functions", SIAM Journal on Computing 33(3), 2004 (Lemma 2.6, stated for $k$-peelable maps).
