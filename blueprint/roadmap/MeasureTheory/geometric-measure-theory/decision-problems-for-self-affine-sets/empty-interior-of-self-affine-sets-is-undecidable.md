# Empty interior of self-affine sets is undecidable

No algorithm decides whether an attractor of a graph-directed iterated function system of affine maps with rational coefficients has empty interior, already for two-dimensional systems on a graph with three vertices.

**Graph-directed iterated function systems.** A $d$-dimensional *graph-directed iterated function system* (GIFS) is a finite directed graph with vertex set $\mathcal Q$ in which each edge $e$ is labeled by a contracting map $f_e:\mathbb R^d\to\mathbb R^d$, that is, one with $\|f_e(x)-f_e(y)\|\le c\|x-y\|$ for some $c<1$. Its *attractors* are the unique nonempty compact sets $(X_q)_{q\in\mathcal Q}$ with

$$
X_q=\bigcup_{r\in\mathcal Q}\ \bigcup_{e\in E_{q,r}}f_e(X_r)\qquad(q\in\mathcal Q),
$$

where $E_{q,r}$ is the set of edges from $q$ to $r$; a graph with one vertex gives an ordinary iterated function system and its attractor. The GIFS is *affine* when every $f_e$ is an affine map, and its attractors are then self-affine sets.

**Theorem (Jolivet and Kari).** It is undecidable, given a $d$-dimensional affine GIFS whose maps have rational coefficients and a vertex $q$, whether $X_q$ has empty interior; this remains undecidable for $2$-dimensional GIFS on graphs with $3$ vertices (Theorem 4.2).

The source also proves that it is undecidable whether $X_q=[0,1]^d$, with the same restriction to $2$-dimensional GIFS on $3$ vertices (Theorem 4.1). Both problems remain undecidable for GIFS whose maps have diagonal linear parts whose entries are negative powers of integers (Remark 4.3). It is likewise undecidable, given two vertices $q$ and $r$, whether $X_q\cap X_r$ has empty interior (Remark 4.4).

## Depends on

- [Interior of a subset](../../../Topology/topological-spaces/open-and-closed-sets/interior-of-subset.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Attractor of an iterated function system](../hausdorff-dimension-of-self-similar-sets/is-attractor.md)

## Proof depends on

None.

## Expansion

Following Dube, one associates to a $d$-tape automaton $\mathcal M$ an affine GIFS on its states: a transition from $q$ to $r$ reading words $w_1,\dots,w_d$ becomes the map $x\mapsto\mathrm{diag}(|A_1|^{-|w_1|},\dots,|A_d|^{-|w_d|})\,x+(\Delta_1(w_1),\dots,\Delta_d(w_d))$, where $\Delta_k(w)$ is the number with base-$|A_k|$ expansion $0.w$. The attractor $X_q$ is then the set of points of $[0,1]^d$ with a base expansion accepted from $q$, so $q$ accepts every infinite configuration exactly when $X_q=[0,1]^d$, and $q$ has a universal prefix exactly when $X_q$ has nonempty interior (Proposition 3.7). Universality of a state of a $d$-tape automaton and existence of a universal prefix for a state are undecidable, already for $2$-tape automata with $3$ states (Theorems 2.5 and 2.6 of the same source); this transfers to the attractors. Those two automata results have no pages on main.

## Sources

- T. Jolivet and J. Kari, "Undecidable properties of self-affine sets and multi-tape automata", in *Mathematical Foundations of Computer Science 2014 (MFCS 2014)*, Lecture Notes in Computer Science 8634, pp. 352–364, Springer, 2014, doi:[10.1007/978-3-662-44522-8_30](https://doi.org/10.1007/978-3-662-44522-8_30); read in arXiv:1401.0705v2 ([arXiv](https://arxiv.org/abs/1401.0705v2)), whose numbering is used: the definition of GIFS in the introduction, Definition 3.1 and Proposition 3.7, Theorems 2.5 and 2.6, Theorems 4.1 and 4.2 and Remarks 4.3 and 4.4.
