# Erdős Problem 808 is false

There are real numbers $c > 0$ and $\varepsilon > 0$ such
that for infinitely many natural numbers $n$ there are a set $A$ of $n$ positive integers and a
finite set $E$ of pairs $(a, b)$ with $a, b \in A$ and $a < b$ (the edges of a graph on $A$)
such that $|E| \ge n^{1+c}$ and
$\max(|\{a + b : (a, b) \in E\}|, |\{ab : (a, b) \in E\}|) < n^{1+c-\varepsilon}$.

Alon, Ruzsa and Solymosi constructed, for arbitrarily large $n$, sets of $n$ integers with
graphs of $n^{5/3 - o(1)}$ edges along which both the sums and the products take at most
$n^{4/3 + o(1)}$ values, and counterexamples in $\mathbb{N}$ for every $0 < c < 1$.

## Sources

- T. F. Bloom, Erdős Problems, Problem #808, https://www.erdosproblems.com/808 (status DISPROVED); resolution: N. Alon, I. Ruzsa and J. Solymosi, Sums, products and ratios along the edges of a graph, Publ. Mat. 64 (2020), 143-155, Theorem 3: for arbitrarily large m_0 there are a set A of m ≥ m_0 integers and a graph on A with Ω(m^{5/3}/log^{1/3} m) edges such that |A +_G A| + |A ·_G A| = O((m log m)^{4/3}), refuting their Conjecture 2 (the strong Erdős-Szemerédi conjecture); the construction takes A = {uw/v} for positive integers u, v, w scaled by a common denominator, so A consists of positive integers; Theorem 4 gives counterexamples A ⊂ ℕ for every 0 < c < 1, https://web.math.princeton.edu/~nalon/PDFS/sumprodrat7.pdf.
