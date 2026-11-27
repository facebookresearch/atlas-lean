# Res($k$) lower bounds from boundary expansion

If the clause-variable dependency graph of a $\Delta$-CNF is an $(r,\Delta,0.95\Delta)$-boundary expander and $n^{\delta}(n/(0.4r))^{20k^2}=o(r/k)$, then every Res($k$) refutation of the formula has at least $2^{n^{\delta}}$ lines.

The *dependency graph* of a CNF $\varphi$ is the bipartite graph $G_\varphi=(L,R,E)$ whose left vertices are the clauses, whose right vertices are the variables, and with $(u,v)\in E$ when clause $u$ contains $v$ or $\neg v$. For $S\subseteq L$ let $N(S)$ be its set of neighbours and $\partial(S)$ its set of unique neighbours. A bipartite graph is an $(r,\Delta,c)$-*boundary expander* if every left vertex has degree at most $\Delta$ and every $S\subseteq L$ with $|S|\le r$ has $|\partial(S)|\ge c|S|$.

**Theorem.** Let $\varphi$ be a $\Delta$-CNF on $n$ variables whose dependency graph is an $(r,\Delta,0.95\Delta)$-boundary expander. Then for any $\delta>0$, if

$$
n^{\delta}\Bigl(\frac{n}{0.4\,r}\Bigr)^{20k^2}=o(r/k),
$$

every [Res($k$)](k-dnf-resolution.md) proof of $\varphi$ has size at least $2^{n^{\delta}}$.

## Expansion

The theorem is proved for linear systems $A$ whose graph $G_A$ is an $(r,\Delta,(1-\varepsilon)\Delta)$-boundary expander with $\varepsilon=0.05$, under the condition $n^{\delta}(n/(8\varepsilon r))^{k^2/\varepsilon}=o(r/k)$; with $\varepsilon=0.05$ this is the condition above. The key tool is a closure in expanders and a new measure, the *closure covering number* of a collection of terms. Assuming a short proof, its $k$-DNF lines are turned into "DNF trees" (mixtures of decision trees and DNFs); a random restriction, controlled by a restriction lemma that translates closure-independence of terms into probabilities, makes them perfect DNF trees of small height, and a direct argument bounds the height of such trees from below. Unlike earlier Res($k$) lower bounds, the argument does not go through the small restriction switching lemma and does not reduce to resolution. Unique-neighbour counting ($|N(S)|\le|\partial(S)|+(\Delta|S|-|\partial(S)|)/2$) shows that ordinary expansion $(1-\varepsilon)\Delta$ gives boundary expansion $(1-2\varepsilon)\Delta$. Applied to random CNFs it gives the [random CNF bounds](res-k-lower-bounds-for-random-cnf.md).

## Depends on

- [k-DNF resolution Res(k)](k-dnf-resolution.md)

## Proof depends on

- [Unique-neighbour lemma for bipartite vertex expanders](../../../../GraphTheory/algebraic-graph-theory/spectral-expansion-and-connectivity/unique-neighbour-lemma.md)

## Sources

- Anastasia Sofronova and Dmitry Sokolov, "A Lower Bound for k-DNF Resolution on Random CNF Formulas via Expansion", *40th Computational Complexity Conference (CCC 2025)*, LIPIcs vol. 339, paper 32, 2025, https://doi.org/10.4230/LIPIcs.CCC.2025.32; numbering as in the [ECCC Report TR22-054 edition](https://eccc.weizmann.ac.il/report/2022/054/) (Section 3, definitions of expanders and boundary expanders; Section 4, dependency graph; Theorem 1.1 and Theorem 5.1 (reformulation)).
